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

let object_declaration_hook = ref []
let add_object_declaration_hook f =
 object_declaration_hook := f :: !object_declaration_hook

exception AlreadyDefined of UriManager.uri

type coercion_decl = 
  UriManager.uri -> int (* arity *) ->
   int (* saturations *) -> string (* baseuri *) ->
    UriManager.uri list (* lemmas (new objs) *)

  
let stack = ref [];;

let push () =
  stack := CoercDb.dump () :: !stack;
  CoercDb.restore CoercDb.empty_coerc_db;
;;

let pop () =
  match !stack with
  | [] -> raise (Failure "Unable to POP from librarySync.ml")
  | db :: tl -> 
      stack := tl;
      CoercDb.restore db;
;;

let uris_of_obj uri =
 let innertypesuri = UriManager.innertypesuri_of_uri uri in
 let bodyuri = UriManager.bodyuri_of_uri uri in
 let univgraphuri = UriManager.univgraphuri_of_uri uri in
  innertypesuri,bodyuri,univgraphuri

let paths_and_uris_of_obj uri =
  let resolved = Http_getter.filename' ~local:true ~writable:true uri in
  let basepath = Filename.dirname resolved in
  let innertypesuri, bodyuri, univgraphuri = uris_of_obj uri in
  let innertypesfilename=(UriManager.nameext_of_uri innertypesuri)^".xml.gz"in
  let innertypespath = basepath ^ "/" ^ innertypesfilename in
  let xmlfilename = (UriManager.nameext_of_uri uri) ^ ".xml.gz" in
  let xmlpath = basepath ^ "/" ^ xmlfilename in
  let xmlbodyfilename = (UriManager.nameext_of_uri uri) ^ ".body.xml.gz" in
  let xmlbodypath = basepath ^ "/" ^  xmlbodyfilename in
  let xmlunivgraphfilename=(UriManager.nameext_of_uri univgraphuri)^".xml.gz"in
  let xmlunivgraphpath = basepath ^ "/" ^ xmlunivgraphfilename in
  xmlpath, xmlbodypath, innertypespath, bodyuri, innertypesuri, 
  xmlunivgraphpath, univgraphuri

let save_object_to_disk uri obj ugraph univlist =
  assert false (*
  let write f x =
    if not (Helm_registry.get_opt_default 
              Helm_registry.bool "matita.nodisk" ~default:false) 
    then      
      f x
  in
  let ensure_path_exists path =
    let dir = Filename.dirname path in
    HExtlib.mkdir dir
  in
  (* generate annobj, ids_to_inner_sorts and ids_to_inner_types *)
  let annobj, innertypes, ids_to_inner_sorts, generate_attributes =
   if Helm_registry.get_bool "matita.system" &&
      not (Helm_registry.get_bool "matita.noinnertypes")
   then
    let annobj, _, _, ids_to_inner_sorts, ids_to_inner_types, _, _ =
     Cic2acic.acic_object_of_cic_object obj 
    in
    let innertypesxml = 
     Cic2Xml.print_inner_types
      uri ~ids_to_inner_sorts ~ids_to_inner_types ~ask_dtd_to_the_getter:false
    in
    annobj, Some innertypesxml, Some ids_to_inner_sorts, false
   else 
    let annobj = Cic2acic.plain_acic_object_of_cic_object obj in  
    annobj, None, None, true 
  in 
  (* prepare XML *)
  let xml, bodyxml =
   Cic2Xml.print_object
    uri ?ids_to_inner_sorts ~ask_dtd_to_the_getter:false 
    ~generate_attributes annobj 
  in    
  let xmlpath, xmlbodypath, innertypespath, bodyuri, innertypesuri, 
      xmlunivgraphpath, univgraphuri = 
    paths_and_uris_of_obj uri 
  in
  write (List.iter HExtlib.mkdir) (List.map Filename.dirname [xmlpath]);
  (* now write to disk *)
  write ensure_path_exists xmlpath;
  write (Xml.pp ~gzip:true xml) (Some xmlpath);
  write (CicUniv.write_xml_of_ugraph xmlunivgraphpath ugraph) univlist;
  (* we return a list of uri,path we registered/created *)
  (uri,xmlpath) ::
  (univgraphuri,xmlunivgraphpath) ::
    (* now the optional inner types, both write and register *)
    (match innertypes with 
     | None -> []
     | Some innertypesxml ->
         write ensure_path_exists innertypespath;
         write (Xml.pp ~gzip:true innertypesxml) (Some innertypespath);
         [innertypesuri, innertypespath]
    ) @
    (* now the optional body, both write and register *)
    (match bodyxml,bodyuri with
       None,_ -> []
     | Some bodyxml,Some bodyuri->
         write ensure_path_exists xmlbodypath;
         write (Xml.pp ~gzip:true bodyxml) (Some xmlbodypath);
         [bodyuri, xmlbodypath]
     | _-> assert false) 
     *)


let typecheck_obj =
 let profiler = HExtlib.profile "add_obj.typecheck_obj" in
  fun uri obj ->
  assert false (* MATITA 1.0
     profiler.HExtlib.profile (CicTypeChecker.typecheck_obj uri) obj
  *)

let index_obj =
 let profiler = HExtlib.profile "add_obj.index_obj" in
  fun ~dbd ~uri ->
  assert false (* MATITA 1.0
   profiler.HExtlib.profile (fun uri -> MetadataDb.index_obj ~dbd ~uri) uri
   *)

let remove_obj uri =
  assert false (* MATITA 1.0
  let derived_uris_of_uri uri =
   let innertypesuri, bodyuri, univgraphuri = uris_of_obj uri in
    innertypesuri::univgraphuri::(match bodyuri with None -> [] | Some u -> [u])
  in
  let uris_to_remove =
   if UriManager.uri_is_ind uri then LibraryDb.xpointers_of_ind uri else [uri]
  in
  let files_to_remove = uri :: derived_uris_of_uri uri in   
  List.iter 
   (fun uri -> 
     (try
       let file = Http_getter.resolve' ~local:true ~writable:true uri in
        HExtlib.safe_remove file;
        HExtlib.rmdir_descend (Filename.dirname file)
     with Http_getter_types.Key_not_found _ -> ());
   ) files_to_remove ;
  List.iter (fun uri -> ignore (LibraryDb.remove_uri uri)) uris_to_remove ;
  CicEnvironment.remove_obj uri
;;
*)

let rec add_obj uri obj ~pack_coercion_obj =
  assert false (* MATITA 1.0
  let obj = 
    if CoercDb.is_a_coercion (Cic.Const (uri, [])) = None
    then pack_coercion_obj obj
    else obj 
  in
  let dbd = LibraryDb.instance () in
  if CicEnvironment.in_library uri then raise (AlreadyDefined uri);
  begin (* ATOMIC *)
    typecheck_obj uri obj; (* 1 *)
    let obj, ugraph, univlist = 
      try CicEnvironment.get_cooked_obj_with_univlist CicUniv.empty_ugraph uri 
      with CicEnvironment.Object_not_found _ -> assert false
    in
    try 
      index_obj ~dbd ~uri; (* 2 must be in the env *)
      try
        (*3*)
        let new_stuff = save_object_to_disk uri obj ugraph univlist in
        try 
         HLog.message
          (Printf.sprintf "%s defined" (UriManager.string_of_uri uri))
        with exc ->
          List.iter HExtlib.safe_remove (List.map snd new_stuff); (* -3 *)
          raise exc
      with exc ->
        ignore(LibraryDb.remove_uri uri); (* -2 *)
        raise exc
    with exc ->
      CicEnvironment.remove_obj uri; (* -1 *)
      raise exc
  end; 
  let added = ref [] in
  let add_obj_with_parachute u o =
    added := u :: !added;
    add_obj u o ~pack_coercion_obj in
  let old_db = CoercDb.dump () in
  try
    List.fold_left 
      (fun lemmas f ->
        f ~add_obj:add_obj_with_parachute 
        ~add_coercion:(add_coercion ~add_composites:true ~pack_coercion_obj)
        uri obj @ lemmas)
      [] !object_declaration_hook
  with exn -> 
    List.iter remove_obj !added;
    remove_obj uri;
    CoercDb.restore old_db;
    raise exn
  (* /ATOMIC *)
    *)

and
 add_coercion ~add_composites ~pack_coercion_obj uri arity saturations baseuri 
=
  assert false (* MATITA 1.0
  let coer_ty,_ =
    let coer = CicUtil.term_of_uri uri in
    CicTypeChecker.type_of_aux' [] [] coer CicUniv.oblivion_ugraph 
  in
  (* we have to get the source and the tgt type uri
   * in Coq syntax we have already their names, but
   * since we don't support Funclass and similar I think
   * all the coercion should be of the form
   * (A:?)(B:?)T1->T2
   * So we should be able to extract them from the coercion type
   * 
   * Currently only (_:T1)T2 is supported.
   * should we saturate it with metas in case we insert it?
   * 
   *)
  let spine2list ty =
    let rec aux = function
      | Cic.Prod( _, src, tgt) -> src::aux tgt
      | t -> [t]
    in
    aux ty
  in
  let src_carr, tgt_carr, no_args = 
    let get_classes arity saturations l = 
      (* this is the ackerman's function revisited *)
      let rec aux = function
         0,0,None,tgt::src::_ -> src,Some (`Class tgt)
       | 0,0,target,src::_ -> src,target
       | 0,saturations,None,tgt::tl -> aux (0,saturations,Some (`Class tgt),tl)
       | 0,saturations,target,_::tl -> aux (0,saturations - 1,target,tl)
       | arity,saturations,None,_::tl -> 
            aux (arity, saturations, Some `Funclass, tl)
       | arity,saturations,target,_::tl -> 
            aux (arity - 1, saturations, target, tl)
       | _ -> assert false
      in
       aux (arity,saturations,None,List.rev l)
    in
    let types = spine2list coer_ty in
    let src,tgt = get_classes arity saturations types in
     CoercDb.coerc_carr_of_term (CicReduction.whd ~delta:false [] src) 0,
     (match tgt with
     | None -> assert false
     | Some `Funclass -> CoercDb.coerc_carr_of_term (Cic.Implicit None) arity
     | Some (`Class tgt) ->
         CoercDb.coerc_carr_of_term (CicReduction.whd ~delta:false [] tgt) 0),
     List.length types - 1
  in
  let already_in_obj src_carr tgt_carr uri obj = 
     List.exists 
      (fun (s,t,ul) -> 
        if not (CoercDb.eq_carr s src_carr && 
                CoercDb.eq_carr t tgt_carr)
        then false 
        else
        List.exists 
         (fun u,_,_ -> 
           let bo, ty = 
            match obj with 
            | Cic.Constant (_, Some bo, ty, _, _) -> bo, ty
            | _ -> 
               (* this is not a composite coercion, thus the uri is valid *)
              let bo = CicUtil.term_of_uri uri in
              bo,
              fst (CicTypeChecker.type_of_aux' [] [] bo
              CicUniv.oblivion_ugraph)
           in
           let are_body_convertible =
            fst (CicReduction.are_convertible [] (CicUtil.term_of_uri u) bo
                  CicUniv.oblivion_ugraph)
           in
           if not are_body_convertible then
             (HLog.warn
              ("Coercions " ^ 
               UriManager.string_of_uri u ^ " and " ^ UriManager.string_of_uri
               uri^" are not convertible, but are between the same nodes.\n"^
               "From now on unification can fail randomly.");
             false)
           else
             match t, tgt_carr with
             | CoercDb.Sort (Cic.Type i), CoercDb.Sort (Cic.Type j)
             | CoercDb.Sort (Cic.CProp i), CoercDb.Sort (Cic.CProp j)
              when not (CicUniv.eq i j) -> 
              (HLog.warn 
               ("Coercion " ^ UriManager.string_of_uri uri ^ " has the same " ^
               "body of " ^ UriManager.string_of_uri u ^ " but lives in a " ^
               "different universe : " ^ 
                 CicUniv.string_of_universe j ^ " <> " ^
                 CicUniv.string_of_universe i); false)
             | CoercDb.Sort Cic.Prop , CoercDb.Sort Cic.Prop 
             | CoercDb.Sort (Cic.Type _) , CoercDb.Sort (Cic.Type _)
             | CoercDb.Sort (Cic.CProp _), CoercDb.Sort (Cic.CProp _) -> 
                (HLog.warn 
                ("Skipping coercion " ^ UriManager.name_of_uri uri ^ " since "^
                 "it is a duplicate of " ^ UriManager.string_of_uri u);
                true) 
             | CoercDb.Sort s1, CoercDb.Sort s2 -> 
              (HLog.warn 
               ("Coercion " ^ UriManager.string_of_uri uri ^ " has the same " ^
               "body of " ^ UriManager.string_of_uri u ^ " but lives in a " ^
               "different universe : " ^ 
                 CicPp.ppterm (Cic.Sort s1) ^ " <> " ^ 
                 CicPp.ppterm (Cic.Sort s2)); false)
             | _ -> 
                let ty', _ = 
                  CicTypeChecker.type_of_aux' [] [] (CicUtil.term_of_uri u) 
                  CicUniv.oblivion_ugraph
                in
                if CicUtil.alpha_equivalence ty ty' then
                (HLog.warn 
                ("Skipping coercion " ^ UriManager.name_of_uri uri ^ " since "^
                 "it is a duplicate of " ^ UriManager.string_of_uri u);
                true)
                else false
                
                )
         ul)
      (CoercDb.to_list (CoercDb.dump ()))
  in
  let cpos = no_args - arity - saturations - 1 in 
  if not add_composites then
    (CoercDb.add_coercion (src_carr, tgt_carr, uri, saturations, cpos); [])
  else
    let _ = 
      if already_in_obj src_carr tgt_carr uri
       (fst (CicEnvironment.get_obj CicUniv.oblivion_ugraph uri)) then
        raise (AlreadyDefined uri);
    in
    let new_coercions = 
      CicCoercion.close_coercion_graph src_carr tgt_carr uri saturations
       baseuri
    in
    let new_coercions = 
      List.filter (fun (s,t,u,_,obj,_,_) -> not(already_in_obj s t u obj))
      new_coercions 
    in
    (* update the DB *)
    let lemmas = 
      List.fold_left
        (fun acc (src,tgt,uri,saturations,obj,arity,cpos) ->
           CoercDb.add_coercion (src,tgt,uri,saturations,cpos);
           let acc = add_obj uri obj pack_coercion_obj @ uri::acc in
           acc)
        [] new_coercions
    in
    CoercDb.add_coercion (src_carr, tgt_carr, uri, saturations, cpos);
(*     CoercDb.prefer uri; *)
    lemmas
    *)
;;

    
