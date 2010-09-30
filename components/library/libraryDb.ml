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

(* $Id$ *)

let dbtype_of_string dbtype =
   if dbtype = "library" then HSql.Library
   else if dbtype = "user" then HSql.User
   else if dbtype = "legacy" then HSql.Legacy
   else raise (HSql.Error "HSql: wrong config file format")

let parse_dbd_conf _ =
  let metadata = Helm_registry.get_list Helm_registry.string "db.metadata" in
  List.map
    (fun s -> 
      match Pcre.split ~pat:"\\s+" s with
      | [path;db;user;pwd;dbtype] -> 
           let dbtype = dbtype_of_string dbtype in
           let pwd = if pwd = "none" then None else Some pwd in
           (* TODO parse port *)
           path, None, db, user, pwd, dbtype
      | _ -> raise (HSql.Error "HSql: Bad format in config file"))
    metadata
;;

let parse_dbd_conf _ =
   HSql.mk_dbspec (parse_dbd_conf ())
;;

let instance =
  let dbd = lazy (
    let dbconf = parse_dbd_conf () in
    HSql.quick_connect dbconf)
  in
  fun () -> Lazy.force dbd
;;

let xpointer_RE = Pcre.regexp "#.*$"
let file_scheme_RE = Pcre.regexp "^file://"

let clean_owner_environment () =
  let dbd = instance () in
  let obj_tbl = MetadataTypes.obj_tbl () in
  let sort_tbl = MetadataTypes.sort_tbl () in
  let rel_tbl = MetadataTypes.rel_tbl () in
  let name_tbl =  MetadataTypes.name_tbl () in
  let count_tbl = MetadataTypes.count_tbl () in
  let tbls = [ 
    (obj_tbl,`RefObj) ; (sort_tbl,`RefSort) ; (rel_tbl,`RefRel) ;
    (name_tbl,`ObjectName) ; (count_tbl,`Count) ] 
  in
  let dbtype = 
    if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
  in
  let statements = 
    (SqlStatements.drop_tables tbls) @ 
    (SqlStatements.drop_indexes tbls dbtype dbd)
  in
  let owned_uris =
    try
      MetadataDb.clean ~dbd
    with (HSql.Error _) as exn ->
      match HSql.errno dbtype dbd with 
      | HSql.No_such_table -> []
      | _ -> raise exn
  in
  List.iter
    (fun uri ->
      let uri = Pcre.replace ~rex:xpointer_RE ~templ:"" uri in
      List.iter
        (fun suffix ->
          try
           HExtlib.safe_remove 
             (Http_getter.resolve ~local:true ~writable:true (uri ^ suffix))
          with Http_getter_types.Key_not_found _ -> ())
        [""; ".body"; ".types"])
    owned_uris;
  List.iter (fun statement -> 
    try
      ignore (HSql.exec dbtype dbd statement)
    with (HSql.Error _) as exn ->
      match HSql.errno dbtype dbd with 
      | HSql.No_such_table
      | HSql.Bad_table_error
      | HSql.No_such_index -> ()
      | _ -> raise exn
    ) statements;
;;

let create_owner_environment () = 
  let dbd = instance () in
  let obj_tbl = MetadataTypes.obj_tbl () in
  let sort_tbl = MetadataTypes.sort_tbl () in
  let rel_tbl = MetadataTypes.rel_tbl () in
  let name_tbl =  MetadataTypes.name_tbl () in
  let count_tbl = MetadataTypes.count_tbl () in
  let l_obj_tbl = MetadataTypes.library_obj_tbl  in
  let l_sort_tbl = MetadataTypes.library_sort_tbl  in
  let l_rel_tbl = MetadataTypes.library_rel_tbl  in
  let l_name_tbl =  MetadataTypes.library_name_tbl  in
  let l_count_tbl = MetadataTypes.library_count_tbl  in
  let tbls = [ 
    (obj_tbl,`RefObj) ; (sort_tbl,`RefSort) ; (rel_tbl,`RefRel) ;
    (name_tbl,`ObjectName) ; (count_tbl,`Count) ]
  in
  let system_tbls = [ 
    (l_obj_tbl,`RefObj) ; (l_sort_tbl,`RefSort) ; (l_rel_tbl,`RefRel) ;
    (l_name_tbl,`ObjectName) ; (l_count_tbl,`Count) ] 
  in
  let tag tag l = List.map (fun x -> tag, x) l in
  let statements = 
    (tag HSql.Library (SqlStatements.create_tables system_tbls)) @ 
    (tag HSql.User (SqlStatements.create_tables tbls)) @ 
    (tag HSql.Library (SqlStatements.create_indexes system_tbls)) @
    (tag HSql.User (SqlStatements.create_indexes tbls))
  in
  List.iter 
    (fun (dbtype, statement) -> 
      try
        ignore (HSql.exec dbtype dbd statement)
      with
        (HSql.Error _) as exc -> 
          let status = HSql.errno dbtype dbd in 
          match status with 
          | HSql.Table_exists_error -> ()
          | HSql.Dup_keyname -> ()
          | HSql.GENERIC_ERROR _ -> 
              prerr_endline statement;
              raise exc
          | _ -> ())
  statements
;;

(* removes uri from the ownerized tables, and returns the list of other objects
 * (theyr uris) that ref the one removed. 
 * AFAIK there is no need to return it, since the MatitaTypes.staus should
 * contain all defined objects. but to double check we do not garbage the
 * metadata...
 *)
let remove_uri uri =
  let obj_tbl = MetadataTypes.obj_tbl () in
  let sort_tbl = MetadataTypes.sort_tbl () in
  let rel_tbl = MetadataTypes.rel_tbl () in
  let name_tbl =  MetadataTypes.name_tbl () in
  (*let conclno_tbl = MetadataTypes.conclno_tbl () in
  let conclno_hyp_tbl = MetadataTypes.fullno_tbl () in*)
  let count_tbl = MetadataTypes.count_tbl () in
  
  let dbd = instance () in
  let suri = UriManager.string_of_uri uri in 
  let dbtype = 
    if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
  in
  let query table suri = 
    if HSql.isMysql dbtype dbd then 
      Printf.sprintf "DELETE QUICK LOW_PRIORITY FROM %s WHERE source='%s'" table 
        (HSql.escape dbtype dbd suri)
    else 
      Printf.sprintf "DELETE FROM %s WHERE source='%s'" table 
        (HSql.escape dbtype dbd suri)
  in
  List.iter (fun t -> 
    try 
      ignore (HSql.exec dbtype dbd (query t suri))
    with
      exn -> raise exn (* no errors should be accepted *)
    )
  [obj_tbl;sort_tbl;rel_tbl;name_tbl;(*conclno_tbl;conclno_hyp_tbl*)count_tbl];
;;

let xpointers_of_ind uri =
  let dbd = instance () in
  let name_tbl =  MetadataTypes.name_tbl () in
  let dbtype = 
    if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
  in
  let escape s =
    Pcre.replace ~pat:"([^\\\\])_" ~templ:"$1\\_" 
      (HSql.escape dbtype dbd s)
  in
  let query = Printf.sprintf 
    ("SELECT source FROM %s WHERE source LIKE '%s#xpointer%%' "
     ^^ HSql.escape_string_for_like dbtype dbd)
    name_tbl (escape (UriManager.string_of_uri uri))
  in
  let rc = HSql.exec dbtype dbd query in
  let l = ref [] in
  HSql.iter rc (fun a ->  match a.(0) with None ->()|Some a -> l := a:: !l);
  List.map UriManager.uri_of_string !l

