(* Copyright (C) 2004-2005, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

(* HELPERS *)

let create_all dbd =
  let obj_tbl = MetadataTypes.obj_tbl () in
  let sort_tbl = MetadataTypes.sort_tbl () in
  let rel_tbl = MetadataTypes.rel_tbl () in
  let name_tbl =  MetadataTypes.name_tbl () in
  let count_tbl = MetadataTypes.count_tbl () in
  let tbls = [ 
    (obj_tbl,`RefObj) ; (sort_tbl,`RefSort) ; (rel_tbl,`RefRel) ;
    (name_tbl,`ObjectName) ; (count_tbl,`Count) ] 
  in
  let statements = 
    (SqlStatements.create_tables tbls) @ 
    (SqlStatements.create_indexes tbls)
  in
  List.iter (fun statement -> 
    try
      ignore (HSql.exec HSql.Library dbd statement)
    with
      HSql.Error _ as exn -> 
         match HSql.errno HSql.Library dbd with 
         | HSql.Table_exists_error -> ()
         | HSql.OK -> ()
         | _ -> raise exn
      ) statements

let drop_all dbd =
  let obj_tbl = MetadataTypes.obj_tbl () in
  let sort_tbl = MetadataTypes.sort_tbl () in
  let rel_tbl = MetadataTypes.rel_tbl () in
  let name_tbl =  MetadataTypes.name_tbl () in
  let count_tbl = MetadataTypes.count_tbl () in
  let tbls = [ 
    (obj_tbl,`RefObj) ; (sort_tbl,`RefSort) ; (rel_tbl,`RefRel) ;
    (name_tbl,`ObjectName) ; (count_tbl,`Count) ] 
  in
  let statements = 
    (SqlStatements.drop_tables tbls) @ 
    (SqlStatements.drop_indexes tbls HSql.Library dbd)
  in
  List.iter (fun statement -> 
    try
      ignore (HSql.exec HSql.Library dbd statement)
    with HSql.Error _ as exn ->
      match HSql.errno HSql.Library dbd with 
      | HSql.Bad_table_error 
      | HSql.No_such_index | HSql.No_such_table -> () 
      | _ -> raise exn
    ) statements
  
let slash_RE = Str.regexp "/"
    
let partition l = 
  let l = List.fast_sort Pervasives.compare l in
  let matches s1 s2 =
    let l1,l2 = Str.split slash_RE s1, Str.split slash_RE s2 in
    match l1,l2 with
    | _::x::_,_::y::_ -> x = y 
    | _ -> false
  in
  let rec chunk l =
    match l with
    | [] -> [],[]
    | h::(h1::tl as rest) when matches h h1 -> 
        let ch,todo = chunk rest in
        (h::ch),todo
    | h::(h1::tl as rest)-> [h],rest
    | h::_ -> [h],[]
  in
  let rec split l = 
    let ch, todo = chunk l in
    match todo with
    | [] -> [ch]
    | _ -> ch :: split todo
  in
  split l
  
    
(* ARGV PARSING *)

let _ = 
  try
  if Sys.argv.(1) = "-h"||Sys.argv.(1) = "-help"||Sys.argv.(1) = "--help" then
    begin
    prerr_endline "
usage: ./extractor_manager[.opt] [processes] [owner]

defaults:
  processes = 2
  owner = NEW

"; 
    exit 1
    end
  with Invalid_argument _ -> ()

let processes = 
  try
    int_of_string (Sys.argv.(1))
  with 
    Invalid_argument _ -> 2

let owner =
  try
    Sys.argv.(2)
  with Invalid_argument _ -> "NEW"

let create_peons i =
  let rec aux = function
    | 0 -> []
    | n -> (n,0) :: aux (n-1)
  in
  ref (aux i)

let is_a_peon_idle peons =
  List.exists (fun (_,x) -> x = 0) !peons

let get_ide_peon peons =
  let p = fst(List.find (fun (_,x) -> x = 0) !peons) in
  peons := List.filter (fun (x,_) -> x <> p) !peons;
  p
 
let assign_peon peon pid peons =
  peons := (peon,pid) :: !peons
  
let wait_a_peon peons =
  let pid,status = Unix.wait () in
  (match status with
  | Unix.WEXITED 0 -> ()
  | Unix.WEXITED s ->
      prerr_endline (Printf.sprintf "PEON %d EXIT STATUS %d" pid s)
  | Unix.WSIGNALED s -> 
      prerr_endline 
       (Printf.sprintf "PEON %d HAD A PROBLEM, KILLED BY SIGNAL %d" pid s)
  | Unix.WSTOPPED s -> 
      prerr_endline 
       (Printf.sprintf "PEON %d HAD A PROBLEM, STOPPED BY %d" pid s));
  let p = fst(List.find (fun (_,x) -> x = pid) !peons) in
  peons := List.filter (fun (x,_) -> x <> p) !peons;
  peons := (p,0) :: !peons
 
let is_a_peon_busy peons =
  List.exists (fun (_,x) -> x <> 0) !peons
  
(* MAIN *)
let main () =
      Helm_registry.load_from "extractor.conf.xml";
      Http_getter.init ();
      print_endline "Updating the getter....";
      let base = (Helm_registry.get "tmp.dir") ^ "/maps" in
      let formats i = 
        (Helm_registry.get "tmp.dir") ^ "/"^(string_of_int i)^"/maps" 
      in
      for i = 1 to processes do
        let fmt = formats i in
        ignore(Unix.system ("rm -rf " ^ fmt));
        ignore(Unix.system ("mkdir -p " ^ fmt));
        ignore(Unix.system ("cp -r " ^ base ^ " " ^ fmt ^ "/../"));
      done;
      let dbspec = LibraryDb.parse_dbd_conf () in
      let dbd = HSql.quick_connect dbspec in
      MetadataTypes.ownerize_tables owner;
      let uri_RE = Str.regexp ".*\\(ind\\|var\\|con\\)$" in
      drop_all dbd;
      create_all dbd;
      let uris = Http_getter.getalluris () in
      let uris = List.filter (fun u -> Str.string_match uri_RE u 0) uris in
      let todo = partition uris in
      let cur = ref 0 in
      let tot = List.length todo in
      let peons = create_peons processes in
      print_string "START "; flush stdout;
      ignore(Unix.system "date");
      while !cur < tot do
        if is_a_peon_idle peons then
          let peon = get_ide_peon peons in
          let fmt = formats peon in
          let oc = open_out (fmt ^ "/../todo") in
          List.iter (fun s -> output_string oc (s^"\n")) (List.nth todo !cur);
          close_out oc;
          let pid = Unix.fork () in
          if pid = 0 then
            Unix.execv 
              "./extractor.opt" [| "./extractor.opt" ; fmt ^ "/../" ; owner|]
          else
            begin
              assign_peon peon pid peons;
              incr cur
            end
        else
          wait_a_peon peons
      done;
      while is_a_peon_busy peons do wait_a_peon peons done;
      print_string "END "; flush stdout; 
      ignore(Unix.system "date"); 
      (* and now the rename table stuff *)
      let obj_tbl = MetadataTypes.library_obj_tbl in
      let sort_tbl = MetadataTypes.library_sort_tbl in
      let rel_tbl = MetadataTypes.library_rel_tbl in
      let name_tbl =  MetadataTypes.library_name_tbl in
      let count_tbl = MetadataTypes.library_count_tbl in
      let hits_tbl = MetadataTypes.library_hits_tbl in
      let obj_tbl_b = obj_tbl ^ "_BACKUP" in     
      let sort_tbl_b = sort_tbl ^ "_BACKUP" in     
      let rel_tbl_b = rel_tbl ^ "_BACKUP" in
      let name_tbl_b = name_tbl ^ "_BACKUP" in    
      let count_tbl_b = count_tbl ^ "_BACKUP" in    
      let obj_tbl_c = MetadataTypes.obj_tbl () in
      let sort_tbl_c = MetadataTypes.sort_tbl () in
      let rel_tbl_c = MetadataTypes.rel_tbl () in
      let name_tbl_c =  MetadataTypes.name_tbl () in
      let count_tbl_c = MetadataTypes.count_tbl () in
      let stats = 
        SqlStatements.drop_tables [
          (obj_tbl_b,`RefObj);
          (sort_tbl_b,`RefSort);
          (rel_tbl_b,`RefRel);
          (name_tbl_b,`ObjectName);
          (count_tbl_b,`Count);
          (hits_tbl,`Hits) ] @
        SqlStatements.drop_indexes [
          (obj_tbl,`RefObj);
          (sort_tbl,`RefSort);
          (rel_tbl,`RefRel);
          (name_tbl,`ObjectName);
          (count_tbl,`Count);
          (obj_tbl_c,`RefObj);
          (sort_tbl_c,`RefSort);
          (rel_tbl_c,`RefRel);
          (name_tbl_c,`ObjectName);
          (count_tbl_c,`Count);
          (hits_tbl,`Hits) ] HSql.Library dbd @
        SqlStatements.rename_tables [
          (obj_tbl,obj_tbl_b);
          (sort_tbl,sort_tbl_b);
          (rel_tbl,rel_tbl_b);
          (name_tbl,name_tbl_b);
          (count_tbl,count_tbl_b) ] @
        SqlStatements.rename_tables [
          (obj_tbl_c,obj_tbl);
          (sort_tbl_c,sort_tbl);
          (rel_tbl_c,rel_tbl);
          (name_tbl_c,name_tbl);
          (count_tbl_c,count_tbl) ] @
        SqlStatements.create_tables [
          (hits_tbl,`Hits) ] @
        SqlStatements.fill_hits obj_tbl hits_tbl @
        SqlStatements.create_indexes [
          (obj_tbl,`RefObj);
          (sort_tbl,`RefSort);
          (rel_tbl,`RefRel);
          (name_tbl,`ObjectName);
          (count_tbl,`Count);
          (hits_tbl,`Hits) ]
      in
        List.iter (fun statement -> 
          try
            ignore (HSql.exec HSql.Library dbd statement)
          with HSql.Error _ as exn -> 
            match HSql.errno HSql.Library dbd with 
            | HSql.Table_exists_error
            | HSql.Bad_table_error -> ()
            | _ ->
                prerr_endline (Printexc.to_string exn);
                raise exn)
        stats
;;

main ()
