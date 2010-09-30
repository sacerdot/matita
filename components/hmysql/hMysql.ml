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

(* $Id$ *)

type dbd = Mysql.dbd option 
type result = Mysql.result option
type error_code = 
 | OK
 | Table_exists_error
 | Dup_keyname
 | No_such_table
 | No_such_index
 | Bad_table_error
 | GENERIC_ERROR of string
exception Error of string

let profiler = HExtlib.profile "mysql"

let quick_connect ?host ?database ?port ?password ?user () =
 profiler.HExtlib.profile 
   (fun () ->
      Some (Mysql.quick_connect ?host ?database ?port ?password ?user ())) 
   ()
;;

let disconnect = function 
  | None -> ()
  | Some dbd -> profiler.HExtlib.profile Mysql.disconnect dbd

let escape s =
 profiler.HExtlib.profile Mysql.escape s

let exec s dbd =
  match dbd with
  | None -> None 
  | Some dbd -> 
     try 
      Some (profiler.HExtlib.profile (Mysql.exec dbd) s)
     with Mysql.Error s -> raise (Error s)

let map res ~f =
  match res with 
  | None ->  []
  | Some res -> 
      let map f = Mysql.map res ~f in
      profiler.HExtlib.profile map f

let iter res ~f =
  match res with 
  | None ->  	()
  | Some res -> 
      let iter f = Mysql.iter res ~f in
      profiler.HExtlib.profile iter f

let errno = function 
  | None -> GENERIC_ERROR "Mysql.Connection_error"
  | Some dbd -> 
      match Mysql.errno dbd with
      | Mysql.No_such_table -> No_such_table
      | Mysql.Table_exists_error -> Table_exists_error
      | Mysql.Dup_keyname -> Dup_keyname
      | Mysql.No_such_index -> No_such_index
      | Mysql.Bad_table_error -> Bad_table_error
      | _ -> GENERIC_ERROR "Mysql_generic_error"
;;

let isMysql = true

let escape_string_for_like = ("ESCAPE \"\\\\\"" : ('a,'b,'c,'a) format4);;
