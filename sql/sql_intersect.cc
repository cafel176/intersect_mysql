/* Copyright (c) 2001, 2021, Oracle and/or its affiliates.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License, version 2.0,
   as published by the Free Software Foundation.

   This program is also distributed with certain software (including
   but not limited to OpenSSL) that is licensed under separate terms,
   as designated in a particular file or component or in included license
   documentation.  The authors of MySQL hereby grant you an additional
   permission to link the program and your derivative works with the
   separately licensed software that they have included with MySQL.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License, version 2.0, for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA */

/*
  Process query expressions that are composed of

  1. UNION of query blocks, and/or

  2. have ORDER BY / LIMIT clauses in more than one level.

  An example of 2) is:

    (SELECT * FROM t1 ORDER BY a LIMIT 10) ORDER BY b LIMIT 5
*/

#include "sql/sql_intersect.h"

#include <sys/types.h>

#include <algorithm>
#include <atomic>
#include <cstdio>
#include <cstdlib>  // abort
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "my_alloc.h"
#include "my_base.h"
#include "my_dbug.h"
#include "my_sqlcommand.h"
#include "my_sys.h"
#include "mysql/udf_registration_types.h"
#include "mysqld_error.h"
#include "prealloced_array.h"  // Prealloced_array
#include "scope_guard.h"
#include "sql/auth/auth_acls.h"
#include "sql/basic_row_iterators.h"
#include "sql/composite_iterators.h"
#include "sql/current_thd.h"
#include "sql/debug_sync.h"  // DEBUG_SYNC
#include "sql/field.h"
#include "sql/handler.h"
#include "sql/item.h"
#include "sql/item_subselect.h"
#include "sql/item_sum.h"
#include "sql/join_optimizer/access_path.h"
#include "sql/join_optimizer/explain_access_path.h"
#include "sql/join_optimizer/join_optimizer.h"
#include "sql/mem_root_array.h"
#include "sql/mysqld.h"
#include "sql/opt_explain.h"  // explain_no_table
#include "sql/opt_explain_format.h"
#include "sql/opt_trace.h"
#include "sql/parse_tree_node_base.h"
#include "sql/parse_tree_nodes.h"  // PT_with_clause
#include "sql/pfs_batch_mode.h"
#include "sql/protocol.h"
#include "sql/query_options.h"
#include "sql/row_iterator.h"
#include "sql/sql_base.h"  // fill_record
#include "sql/sql_class.h"
#include "sql/sql_cmd.h"
#include "sql/sql_const.h"
#include "sql/sql_error.h"
#include "sql/sql_executor.h"
#include "sql/sql_lex.h"
#include "sql/sql_list.h"
#include "sql/sql_optimizer.h"  // JOIN
#include "sql/sql_select.h"
#include "sql/sql_tmp_table.h"   // tmp tables
#include "sql/table_function.h"  // Table_function
#include "sql/thd_raii.h"
#include "sql/timing_iterator.h"
#include "sql/window.h"  // Window
#include "template_utils.h"

using std::move;
using std::vector;

class Item_rollup_group_item;
class Item_rollup_sum_switcher;
class Opt_trace_context;

bool Query_result_intersect::prepare(THD *, const mem_root_deque<Item *> &,
                                 Query_expression *u) {
  unit = u;
  return false;
}

bool Query_result_intersect::send_data(THD *thd,
                                   const mem_root_deque<Item *> &values) {
  if (fill_record(thd, table, table->visible_field_ptr(), values, nullptr,
                  nullptr, false))
    return true; /* purecov: inspected */

  if (!check_unique_constraint(table)) return false;

  const int error = table->file->ha_write_row(table->record[0]);
  if (!error) {
    m_rows_in_table++;
    return false;
  }
  // create_ondisk_from_heap will generate error if needed
  if (!table->file->is_ignorable_error(error)) {
    bool is_duplicate;
    if (create_ondisk_from_heap(thd, table, error, true, &is_duplicate))
      return true; /* purecov: inspected */
    // Table's engine changed, index is not initialized anymore
    if (table->hash_field) table->file->ha_index_init(0, false);
    if (!is_duplicate) m_rows_in_table++;
  }
  return false;
}

bool Query_result_intersect::send_eof(THD *) { return false; }

bool Query_result_intersect::flush() { return false; }

/**
  Create a temporary table to store the result of a query expression
  (used, among others, when materializing a UNION DISTINCT).

  @param thd_arg            thread handle
  @param column_types       a list of items used to define columns of the
                            temporary table
  @param is_union_distinct  if set, the temporary table will eliminate
                            duplicates on insert
  @param options            create options
  @param table_alias        name of the temporary table
  @param bit_fields_as_long convert bit fields to ulonglong
  @param create_table If false, a table handler will not be created when
                      creating the result table.

  @details
    Create a temporary table that is used to store the result of a UNION,
    derived table, or a materialized cursor.

  @returns false if table created, true if error
*/

bool Query_result_intersect::create_result_table(
    THD *thd_arg, const mem_root_deque<Item *> &column_types,
    bool is_intersect_distinct, ulonglong options, const char *table_alias,
    bool bit_fields_as_long, bool create_table) {
  mem_root_deque<Item *> visible_fields(thd_arg->mem_root);
  for (Item *item : VisibleFields(column_types)) {
    visible_fields.push_back(item);
  }

  assert(table == nullptr);
  tmp_table_param = Temp_table_param();
  count_field_types(thd_arg->lex->current_query_block(), &tmp_table_param,
                    visible_fields, false, true);
  tmp_table_param.skip_create_table = !create_table;
  tmp_table_param.bit_fields_as_long = bit_fields_as_long;
  if (unit != nullptr) {
    if (unit->is_recursive()) {
      /*
        If the UNIQUE key specified for UNION DISTINCT were a primary key in
        InnoDB, rows would be returned by the scan in an order depending on
        their columns' values, not in insertion order.
      */
      tmp_table_param.can_use_pk_for_unique = false;
    }
    if (unit->mixed_intersect_operators()) {
      // If we have mixed UNION DISTINCT / UNION ALL, we can't use an unique
      // index to deduplicate, as we need to be able to turn off deduplication
      // checking when we get to the UNION ALL part. The handler supports
      // turning off indexes (and the pre-iterator executor used this to
      // implement mixed DISTINCT/ALL), but not selectively, and we might very
      // well need the other indexes when querying against the table.
      // (Also, it would be nice to be able to remove this functionality
      // altogether from the handler.) Thus, we do it manually instead.
      tmp_table_param.force_hash_field_for_unique = true;
    }
  }

  if (!(table = create_tmp_table(thd_arg, &tmp_table_param, visible_fields,
                                 nullptr, is_intersect_distinct, true, options,
                                 HA_POS_ERROR, table_alias)))
    return true;
  if (create_table) {
    table->file->ha_extra(HA_EXTRA_IGNORE_DUP_KEY);
    if (table->hash_field) table->file->ha_index_init(0, false);
  }
  return false;
}

/**
  Reset and empty the temporary table that stores the materialized query result.

  @note The cleanup performed here is exactly the same as for the two temp
  tables of JOIN - exec_tmp_table_[1 | 2].
*/

bool Query_result_intersect::reset() {
  m_rows_in_table = 0;
  return table ? table->empty_result_table() : false;
}
