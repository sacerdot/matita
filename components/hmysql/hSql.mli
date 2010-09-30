(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

type dbd
type result
type error_code =
 | OK
 | Table_exists_error
 | Dup_keyname
 | No_such_table
 | No_such_index
 | Bad_table_error
 | GENERIC_ERROR of string

exception Error of string

(* the exceptions raised are from the Mysql module *)

type dbtype = User | Library | Legacy

  (* host port dbname user password type *)
type dbspec

val mk_dbspec :
  (string * int option * string * string * string option * dbtype) list ->
    dbspec  

val quick_connect : dbspec -> dbd

val disconnect : dbd -> unit

val exec: dbtype -> dbd -> string -> result
val map : result -> f:(string option array -> 'a) -> 'a list
val iter : result -> f:(string option array -> unit) -> unit


val errno : dbtype -> dbd -> error_code
(* val status : dbd -> Mysql.status *)

val escape: dbtype -> dbd -> string -> string

val escape_string_for_like: dbtype -> dbd -> ('a,'b,'c,'a) format4

val isMysql : dbtype -> dbd -> bool

(* this dbd can't do queries, used only in table_creator *)
val fake_db_for_mysql: dbtype -> dbd

