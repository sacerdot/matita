(* Copyright (C) 2004, HELM Team.
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

open MetadataTypes

open Printf

let format_insert dbtype dbd tbl tuples = 
     if HSql.isMysql dbtype dbd then 
	[sprintf "INSERT %s VALUES %s;" tbl (String.concat "," tuples)]
     else
	List.map (fun tup -> 
		sprintf "INSERT INTO %s VALUES %s;" tbl tup) tuples 
;;

let execute_insert dbd uri (sort_cols, rel_cols, obj_cols) =
  let sort_tuples = 
    List.fold_left (fun s l -> match l with
      | [`String a; `String b; `Int c; `String d] -> 
          sprintf "(\"%s\", \"%s\", %d, \"%s\")" a b c d :: s
      | _ -> assert false )
    [] sort_cols
  in
  let rel_tuples =
    List.fold_left (fun s l -> match l with
      | [`String a; `String b; `Int c] ->
          sprintf "(\"%s\", \"%s\", %d)" a b c :: s
      | _ -> assert false)
    [] rel_cols  
  in
  let obj_tuples = List.fold_left (fun s l -> match l with
      | [`String a; `String b; `String c; `Int d] ->
          sprintf "(\"%s\", \"%s\", \"%s\", %d)" a b c d :: s
      | [`String a; `String b; `String c; `Null] ->
          sprintf "(\"%s\", \"%s\", \"%s\", %s)" a b c "NULL" :: s
      | _ -> assert false)
    [] obj_cols
  in
  let dbtype = 
    if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
  in
  if sort_tuples <> [] then
    begin
    let query_sort = 
     format_insert dbtype dbd (sort_tbl ())  sort_tuples 
    in
    List.iter (fun query -> ignore (HSql.exec dbtype dbd query)) query_sort
    end;
  if rel_tuples <> [] then
    begin
    let query_rel = 
     format_insert dbtype dbd (rel_tbl ())  rel_tuples 
    in
    List.iter (fun query -> ignore (HSql.exec dbtype dbd query)) query_rel
    end;
  if obj_tuples <> [] then
    begin
    let query_obj = 
     format_insert dbtype dbd (obj_tbl ())  obj_tuples 
    in
    List.iter (fun query -> ignore (HSql.exec dbtype dbd query)) query_obj
    end
  
    
let count_distinct position l =
  MetadataConstraints.UriManagerSet.cardinal
  (List.fold_left (fun acc d -> 
    match position with
    | `Conclusion -> 
         (match d with
         | `Obj (name,`InConclusion) 
         | `Obj (name,`MainConclusion _ ) -> 
             MetadataConstraints.UriManagerSet.add name acc
         | _ -> acc)
    | `Hypothesis ->
        (match d with
        | `Obj (name,`InHypothesis) 
        | `Obj (name,`MainHypothesis _) -> 
            MetadataConstraints.UriManagerSet.add name acc
        | _ -> acc)
    | `Statement ->
        (match d with
        | `Obj (name,`InBody) -> acc
        | `Obj (name,_) -> MetadataConstraints.UriManagerSet.add name acc
        | _ -> acc)
    ) MetadataConstraints.UriManagerSet.empty l)

let insert_const_no ~dbd l =
 let data =
  List.fold_left
   (fun acc (uri,_,metadata) -> 
     let no_concl = count_distinct `Conclusion metadata in
     let no_hyp = count_distinct `Hypothesis metadata in
     let no_full = count_distinct `Statement metadata in
      (sprintf "(\"%s\", %d, %d, %d)" 
       (UriManager.string_of_uri uri) no_concl no_hyp no_full) :: acc
   ) [] l in
 let dbtype = 
   if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
 in
 let insert =
  format_insert dbtype dbd (count_tbl ())  data
 in
  List.iter (fun query -> ignore (HSql.exec dbtype dbd query)) insert
  
let insert_name ~dbd l =
 let dbtype =
   if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
 in
 let data =
  List.fold_left
   (fun acc (uri,name,_) -> 
      (sprintf "(\"%s\", \"%s\")" (UriManager.string_of_uri uri) name) :: acc
   ) [] l in
 let insert =
   format_insert dbtype dbd (name_tbl ())  data
 in
  List.iter (fun query -> ignore (HSql.exec dbtype dbd query)) insert

type columns =
  MetadataPp.t list list * MetadataPp.t list list * MetadataPp.t list list

  (* TODO ZACK: verify if an object has already been indexed *)
let already_indexed _ = false

(***** TENTATIVE HACK FOR THE DB SLOWDOWN - BEGIN *******)
let analyze_index = ref 0
let eventually_analyze dbd =
  incr analyze_index;
  if !analyze_index > 30 then
    if  HSql.isMysql HSql.User dbd then
    begin
      let analyze t = "OPTIMIZE TABLE " ^ t ^ ";" in
      List.iter 
        (fun table -> ignore (HSql.exec HSql.User dbd (analyze table)))
        [name_tbl (); rel_tbl (); sort_tbl (); obj_tbl(); count_tbl()]
    end
  
(***** TENTATIVE HACK FOR THE DB SLOWDOWN - END *******)

let index_obj ~dbd ~uri = 
  if not (already_indexed uri) then begin
    eventually_analyze dbd;
    let metadata = MetadataExtractor.compute_obj uri in
    let uri = UriManager.string_of_uri uri in
    let columns = MetadataPp.columns_of_metadata metadata in
    execute_insert dbd uri (columns :> columns);
    insert_const_no ~dbd metadata;
    insert_name ~dbd metadata
  end
  

let tables_to_clean =
  [sort_tbl; rel_tbl; obj_tbl; name_tbl; count_tbl]

let clean ~(dbd:HSql.dbd) =
  let owned_uris =  (* list of uris in list-of-columns format *)
    let query = sprintf "SELECT source FROM %s" (name_tbl ()) in
    let result = HSql.exec HSql.User dbd query in
    let uris = HSql.map result (fun cols ->
      match cols.(0) with
      | Some src -> src
      | None -> assert false) in
    (* and now some stuff to remove #xpointers and duplicates *)
    uris
  in
  let del_from tbl =
    let escape s =
      Pcre.replace ~pat:"([^\\\\])_" ~templ:"$1\\_" (HSql.escape HSql.User dbd s)
    in
    let query s = 
      sprintf
       ("DELETE FROM %s WHERE source LIKE \"%s%%\" " ^^
        HSql.escape_string_for_like HSql.User dbd)
        (tbl ()) (escape s)
    in
    List.iter
      (fun source_col -> ignore (HSql.exec HSql.User dbd (query source_col)))
      owned_uris
  in
  List.iter del_from tables_to_clean;
  owned_uris

let unindex ~dbd ~uri =
  let uri = UriManager.string_of_uri uri in
  let del_from tbl =
    let escape s =
      Pcre.replace 
        ~pat:"([^\\\\])_" ~templ:"$1\\_" (HSql.escape HSql.User dbd s)
    in
    let query tbl =
      sprintf
       ("DELETE FROM %s WHERE source LIKE \"%s%%\" " ^^
        HSql.escape_string_for_like HSql.User dbd)
       (tbl ()) (escape uri)
    in
    ignore (HSql.exec HSql.User dbd (query tbl))
  in
  List.iter del_from tables_to_clean

