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

(* $Id: hMysql.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

(*
type result = Mysql.result option
*)


let debug = false
let debug_print = 
  if debug then prerr_endline else (fun _ ->())
;;

type result = Sqlite3.row list
type dbd = Sqlite3.db option

type error_code = 
 | OK
 | Table_exists_error
 | Dup_keyname
 | No_such_table
 | No_such_index
 | Bad_table_error
 | GENERIC_ERROR of string

exception Error of string

let profiler = HExtlib.profile "Sqlite3"

let quick_connect 
  is_library
  ?(host = Helm_registry.get "matita.basedir") 
  ?(database = "sqlite") ?port ?password ?user () 
= 
  let username = Helm_registry.get "user.name" in
  let host_mangled = Pcre.replace ~pat:"[/ .]" ~templ:"_" host in
  let find_db _ = 
    let base = "matita.db." ^ username ^ "." ^ host_mangled ^ "." in
    let root = "/dev/shm/" in
    let files = HExtlib.find ~test:(Pcre.pmatch ~pat:(base^"[0-9]+")) root in
    let rec aux = function
      | [] -> 
         debug_print ("HSqlite3: no valid db files found in memory");
         let name = root ^ base ^ string_of_int (Unix.getpid ()) in
         debug_print ("HSqlite3: memory db file name: "^name);
         name, true
      | x::tl -> 
         debug_print ("HSqlite3: found a .db in memory: " ^ x);
         match Array.to_list (Pcre.extract ~pat:"\\.([0-9]+)$" x) with
         | [] | _::_::_::_ -> assert false
         | [_;p] when HExtlib.is_dir ("/proc/" ^ p) -> 
            debug_print ("HSqlite3: found valid db file: " ^ x);
            x, false
         | _ ->
            HLog.warn ("HSqlite3: dead process db file found: " ^ x);
            HLog.warn ("HSqlite3: removing: " ^ x);
            ignore (Sys.command ("rm " ^ x));
            aux tl
    in
      aux files
  in
  let db_name = host ^ "/" ^ database in
  let db_to_open =
    if HExtlib.is_dir "/dev/shm/" && HExtlib.writable_dir "/dev/shm/" 
       && (not is_library) 
    then (
      let tmp_db_name, first_time = find_db () in      
      let cp_to_ram_cmd = "cp " ^ db_name ^ " " ^ tmp_db_name in
      if first_time then 
        if HExtlib.is_regular db_name then ignore (Sys.command cp_to_ram_cmd)
        else debug_print ("HSqlite3: no initial db: " ^ db_name)
      else debug_print "HSqlite3: not copying the db, already in memory";
      let mv_to_disk_cmd _ = 
        if first_time then ignore (Sys.command ("mv "^tmp_db_name^" "^db_name)) 
        else debug_print "HSqlite3: not copying back the db"
      in
      at_exit mv_to_disk_cmd;
      tmp_db_name)
    else
      db_name
  in
  HExtlib.mkdir (Filename.dirname db_to_open);
  let db = Sqlite3.db_open db_to_open in
  (* attach the REGEX function *)
  Sqlite3.create_fun2 db "REGEXP"
      (fun s rex -> 
        try
         match rex, s with
         | Sqlite3.Data.TEXT rex, Sqlite3.Data.BLOB s
         | Sqlite3.Data.TEXT rex, Sqlite3.Data.TEXT s ->
             let r = Str.regexp rex in
             if Str.string_match r s 0 then 
               Sqlite3.Data.INT 1L 
             else 
               Sqlite3.Data.INT 0L
         | _ -> raise (Error "wrong types to 'REGEXP'")
        with Sys.Break -> Sqlite3.Data.INT 0L
          | exn -> HLog.error (Printexc.to_string exn); raise exn);
  Some db
;;

let disconnect db =
  match db with
  | None -> ()
  | Some db -> 
      let b = Sqlite3.db_close db in
      if b=false then debug_print "No Closed DataBase"
;;

(* XXX hack, sqlite has a print "%q" that should be used, but is not bound *)
let escape s = 
  let s_escaped = Pcre.replace ~pat:"'" ~templ:"''" s in
  (*let s_escaped = Pcre.replace ~pat:"([^'])'([^'])" ~templ:"$1''$2" s in*)
  debug_print s;
  debug_print s_escaped;
  s_escaped
;;

let string_of_rc = function
  |Sqlite3.Rc.OK -> "Sqlite3.Rc.OK" 
  |Sqlite3.Rc.ERROR -> "Sqlite3.Rc.ERROR" 
  |Sqlite3.Rc.INTERNAL -> "Sqlite3.Rc.INTERNAL" 
  |Sqlite3.Rc.PERM -> "Sqlite3.Rc.PERM" 
  |Sqlite3.Rc.ABORT -> "Sqlite3.Rc.ABORT" 
  |Sqlite3.Rc.BUSY -> "Sqlite3.Rc.BUSY" 
  |Sqlite3.Rc.LOCKED -> "Sqlite3.Rc.LOCKED" 
  |Sqlite3.Rc.NOMEM -> "Sqlite3.Rc.NOMEM" 
  |Sqlite3.Rc.READONLY -> "Sqlite3.Rc.READONLY" 
  |Sqlite3.Rc.INTERRUPT -> "Sqlite3.Rc.INTERRUPT" 
  |Sqlite3.Rc.IOERR -> "Sqlite3.Rc.IOERR" 
  |Sqlite3.Rc.CORRUPT -> "Sqlite3.Rc.CORRUPT" 
  |Sqlite3.Rc.NOTFOUND -> "Sqlite3.Rc.NOTFOUND" 
  |Sqlite3.Rc.FULL -> "Sqlite3.Rc.FULL" 
  |Sqlite3.Rc.CANTOPEN -> "Sqlite3.Rc.CANTOPEN" 
  |Sqlite3.Rc.PROTOCOL -> "Sqlite3.Rc.PROTOCOL" 
  |Sqlite3.Rc.EMPTY -> "Sqlite3.Rc.EMPTY" 
  |Sqlite3.Rc.SCHEMA -> "Sqlite3.Rc.SCHEMA" 
  |Sqlite3.Rc.TOOBIG -> "Sqlite3.Rc.TOOBIG" 
  |Sqlite3.Rc.CONSTRAINT -> "Sqlite3.Rc.CONSTRAINT" 
  |Sqlite3.Rc.MISMATCH -> "Sqlite3.Rc.MISMATCH" 
  |Sqlite3.Rc.MISUSE -> "Sqlite3.Rc.MISUSE" 
  |Sqlite3.Rc.NOFLS -> "Sqlite3.Rc.NOFLS" 
  |Sqlite3.Rc.AUTH -> "Sqlite3.Rc.AUTH" 
  |Sqlite3.Rc.FORMAT -> "Sqlite3.Rc.FORMAT" 
  |Sqlite3.Rc.RANGE -> "Sqlite3.Rc.RANGE" 
  |Sqlite3.Rc.NOTADB -> "Sqlite3.Rc.NOTADB" 
  |Sqlite3.Rc.ROW -> "Sqlite3.Rc.ROW" 
  |Sqlite3.Rc.DONE -> "Sqlite3.Rc.DONE" 
  |Sqlite3.Rc.UNKNOWN n -> 
    "Sqlite3.Rc.UNKNOWN " ^ string_of_int (Sqlite3.Rc.int_of_unknown n)
;;

let pp_rc rc = debug_print (string_of_rc rc);;

let exec s db =
 debug_print s;
  let stored_result = ref [] in
  let store row =
    stored_result := row :: !stored_result
  in
  match db with
  | None -> [] 
  | Some db ->  
      let rc = 
        profiler.HExtlib.profile (Sqlite3.exec_no_headers db ~cb:store) s 
      in
      match rc with
      | Sqlite3.Rc.OK -> !stored_result
      | _ -> raise (Error (string_of_rc rc ^ ": " ^ Sqlite3.errmsg db ))
;;

let rec map res ~f = 
  let map f = List.map f res in
  profiler.HExtlib.profile map f
;;

let iter res ~f =
  let iter f = List.iter f res in
  profiler.HExtlib.profile iter f
;;

let errno = function 
  | None -> OK
  | Some db -> 
      match Sqlite3.errcode db with
      |Sqlite3.Rc.OK -> OK
      |Sqlite3.Rc.ERROR ->
         let errmsg = (Sqlite3.errmsg db) in
         if Pcre.pmatch errmsg ~pat:"^table .* already exists" then
           Table_exists_error
         else
         if Pcre.pmatch errmsg ~pat:"^index .* already exists" then Dup_keyname
         else if Pcre.pmatch errmsg ~pat:"^no such table: .*" then No_such_table
         else if Pcre.pmatch errmsg ~pat:"^no such index: .*" then No_such_index
         else GENERIC_ERROR errmsg
      |Sqlite3.Rc.INTERNAL |Sqlite3.Rc.PERM |Sqlite3.Rc.ABORT
      |Sqlite3.Rc.BUSY |Sqlite3.Rc.LOCKED |Sqlite3.Rc.NOMEM
      |Sqlite3.Rc.READONLY |Sqlite3.Rc.INTERRUPT |Sqlite3.Rc.IOERR
      |Sqlite3.Rc.CORRUPT |Sqlite3.Rc.NOTFOUND |Sqlite3.Rc.FULL
      |Sqlite3.Rc.CANTOPEN |Sqlite3.Rc.PROTOCOL |Sqlite3.Rc.EMPTY 
      |Sqlite3.Rc.SCHEMA |Sqlite3.Rc.TOOBIG |Sqlite3.Rc.CONSTRAINT
      |Sqlite3.Rc.MISMATCH |Sqlite3.Rc.MISUSE |Sqlite3.Rc.NOFLS
      |Sqlite3.Rc.AUTH |Sqlite3.Rc.FORMAT |Sqlite3.Rc.RANGE
      |Sqlite3.Rc.NOTADB |Sqlite3.Rc.ROW |Sqlite3.Rc.DONE
      |Sqlite3.Rc.UNKNOWN _ -> GENERIC_ERROR "Sqlite3_generic_error"
;;

let isMysql = false

let escape_string_for_like = ("ESCAPE \"\\\"" : ('a,'b,'c,'a) format4);;
