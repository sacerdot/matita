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
type dbimplementation = Mysql of HMysql.dbd | Sqlite of HSqlite3.dbd | FakeMySql
type result = Mysql_rc of HMysql.result | Sqlite_rc of HSqlite3.result | Nothing

  (* host port dbname user password type *)
type dbspec = (string * int option * string * string * string option * dbtype) list
type dbd = (dbtype * dbimplementation) list 

let debug = false;;
let debug_print s = if debug then prerr_endline (Lazy.force s) else ();;

let pp_dbtype = function
  | User -> "User"
  | Library -> "Library"
  | Legacy -> "Legacy"
;;

let mk_dbspec l = l;;

let quick_connect dbspec =
  HExtlib.filter_map 
    (fun (host, port, database, user, password, kind) -> 
      if Pcre.pmatch ~pat:"^file://" host then
        Some (kind, (Sqlite (HSqlite3.quick_connect (kind = Library)
          ~host:(Pcre.replace ~pat:"^file://" host) 
          ?port ~user ~database ?password ())))
      else if Pcre.pmatch ~pat:"^mysql://" host then
        Some (kind, (Mysql (HMysql.quick_connect 
          ~host:(Pcre.replace ~pat:"^mysql://" host)
          ?port ~user ~database ?password ())))
      else 
        None)
    dbspec      
;;

let mk f1 f2 = function 
  | (Sqlite dbd) -> Sqlite_rc (f1 dbd) 
  | (Mysql dbd) -> Mysql_rc (f2 dbd)
  | FakeMySql -> assert false
;;

let mk_u f1 f2 = function 
  | (_, (Sqlite dbd)) -> f1 dbd 
  | (_, (Mysql dbd)) -> f2 dbd
  | (_, FakeMySql) -> assert false
;;

let wrap f x =
  try f x with 
  | HMysql.Error s | HSqlite3.Error s -> raise (Error s)
  | Not_found -> raise (Error "Not_found")
;;

let disconnect dbd = 
  wrap (List.iter (mk_u HSqlite3.disconnect HMysql.disconnect)) dbd
;;

let exec (dbtype : dbtype) (dbd : dbd) (query : string) = 
  try
    debug_print (lazy ("EXEC: " ^ pp_dbtype dbtype ^ "|" ^ query));
    let dbd = List.assoc dbtype dbd in
    wrap (mk (HSqlite3.exec query) (HMysql.exec query)) dbd
  with Not_found -> Nothing
;;

let map result ~f = 
  match result with
  | Mysql_rc rc -> HMysql.map rc ~f
  | Sqlite_rc rc -> HSqlite3.map rc ~f
  | Nothing -> []
;;

let iter result ~f = 
  match result with
  | Mysql_rc rc -> HMysql.iter rc ~f
  | Sqlite_rc rc -> HSqlite3.iter rc ~f
  | Nothing -> ()
;;

let sqlite_err = function 
 | HSqlite3.OK -> OK
 | HSqlite3.Table_exists_error -> Table_exists_error
 | HSqlite3.Dup_keyname -> Dup_keyname
 | HSqlite3.No_such_table -> No_such_table
 | HSqlite3.No_such_index -> No_such_index
 | HSqlite3.Bad_table_error -> Bad_table_error
 | HSqlite3.GENERIC_ERROR s -> GENERIC_ERROR s
;;

let mysql_err = function 
 | HMysql.OK -> OK
 | HMysql.Table_exists_error -> Table_exists_error
 | HMysql.Dup_keyname -> Dup_keyname
 | HMysql.No_such_table -> No_such_table
 | HMysql.No_such_index -> No_such_index
 | HMysql.Bad_table_error -> Bad_table_error
 | HMysql.GENERIC_ERROR s -> GENERIC_ERROR s
;;

let errno dbtype dbd =
  wrap 
    (fun d -> 
    try
      match List.assoc dbtype d with 
      | Mysql dbd -> mysql_err (HMysql.errno dbd)
      | Sqlite dbd -> sqlite_err (HSqlite3.errno dbd)
      | FakeMySql -> assert false
    with Not_found -> OK)
    dbd
;;

let escape dbtype dbd s = 
  try
      match List.assoc dbtype dbd with
      | Mysql _ | FakeMySql -> wrap HMysql.escape s
      | Sqlite _ -> wrap HSqlite3.escape s
  with Not_found -> s
;;

let escape_string_for_like dbtype dbd = 
  try
      match List.assoc dbtype dbd with 
      | Mysql _ | FakeMySql -> HMysql.escape_string_for_like
      | Sqlite _ -> HSqlite3.escape_string_for_like
  with Not_found -> 
    ("ESCAPE \"\\\"" : ('a,'b,'c,'a) format4) 
;;

let isMysql dbtype dbd =
  wrap 
    (fun d -> 
       try
        match List.assoc dbtype d with Mysql _ -> true | _ -> false
       with Not_found -> false) 
    dbd
;;

let fake_db_for_mysql dbtype =
  [dbtype, FakeMySql]  
;;
