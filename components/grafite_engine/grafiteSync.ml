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

open Printf

let is_a_variant obj = 
  match obj with
    | Cic.Constant(_,_,_,_,attrs) ->
	List.exists (fun x -> x = `Flavour `Variant) attrs
    | _ -> false

let uris_for_inductive_type uri obj =
  match obj with 
    | Cic.InductiveDefinition(types,_,_,_) ->
	let suri = UriManager.string_of_uri uri in
	let uris,_ =
	  List.fold_left
	    (fun (acc,i) (_,_,_,constructors)->
	       let is = string_of_int i in	     
	       let newacc,_ =
		 List.fold_left
		   (fun (acc,j) _ ->
		      let js = string_of_int j in
			UriManager.uri_of_string
			  (suri^"#xpointer(1/"^is^"/"^js^")")::acc,j+1) 
		   (acc,1) constructors
	       in
	       newacc,i+1)
	    ([],1) types 
	in uris
    | _ -> [uri] 
;;

let is_equational_fact ty =
  let rec aux ctx t = 
    match CicReduction.whd ctx t with 
    | Cic.Prod (name,src,tgt) ->
        let s,u = 
          CicTypeChecker.type_of_aux' [] ctx src CicUniv.oblivion_ugraph
        in
        if fst (CicReduction.are_convertible ctx s (Cic.Sort Cic.Prop) u) then
          false
        else
          aux (Some (name,Cic.Decl src)::ctx) tgt
    | Cic.Appl [ Cic.MutInd (u,_,_) ; _; _; _] -> LibraryObjects.is_eq_URI u
    | _ -> false
  in 
    aux [] ty
;;
    
let add_obj ~pack_coercion_obj uri obj status =
 let lemmas = LibrarySync.add_obj ~pack_coercion_obj uri obj in
 let add_to_universe (automation_cache,status) uri =
   let term = CicUtil.term_of_uri uri in
   let ty,_ = CicTypeChecker.type_of_aux' [] [] term CicUniv.oblivion_ugraph in
   let tkeys = Universe.keys [] ty in
   let universe = automation_cache.AutomationCache.univ in
   let universe, index_cmd = 
     List.fold_left 
       (fun (universe,acc) key -> 
         let cands = Universe.get_candidates universe key in
         let tys = 
           List.map
              (fun t -> 
                 let ty, _ = 
                   CicTypeChecker.type_of_aux' [] [] t CicUniv.oblivion_ugraph
                 in
                   ty)
              cands
         in
         if List.for_all 
              (fun cty -> 
                 not (fst(CicReduction.are_convertible [] ty cty
                 CicUniv.oblivion_ugraph))) tys 
        then
           Universe.index universe key term,
           GrafiteAst.Index(HExtlib.dummy_floc,(Some key),uri)::acc
         else
           universe, acc)
       (universe,[]) tkeys
   in
   let is_equational = is_equational_fact ty in
   let select_cmd = 
      if is_equational then
       [ GrafiteAst.Select(HExtlib.dummy_floc,uri) ]
      else
       []
   in
   let automation_cache = 
     if is_equational then
        AutomationCache.add_term_to_active automation_cache [] [] [] term None
     else
        automation_cache
   in
   let automation_cache = 
     { automation_cache with AutomationCache.univ = universe }  in
   let status = GrafiteTypes.add_moo_content index_cmd status in
   let status = GrafiteTypes.add_moo_content select_cmd status in
   (automation_cache,status)
 in
 let uris_to_index = 
   if is_a_variant obj then []
   else (uris_for_inductive_type uri obj) @ lemmas 
 in
 let automation_cache,status =
   List.fold_left add_to_universe 
     (status#automation_cache,status) 
     uris_to_index 
 in
  (status
    #set_objects (uri :: lemmas @ status#objects))
    #set_automation_cache automation_cache,
  lemmas

let add_coercion ~pack_coercion_obj ~add_composites status uri arity
 saturations baseuri
=
 let lemmas = 
   LibrarySync.add_coercion ~add_composites ~pack_coercion_obj 
    uri arity saturations baseuri in
 let status = 
  (status
    #set_coercions (CoercDb.dump ())) ; 
    #set_objects (lemmas @ status#objects)
 in
 let status = NCicCoercion.index_old_db (CoercDb.dump ()) status in
  status, lemmas

let prefer_coercion status u = 
  CoercDb.prefer u;
   status#set_coercions (CoercDb.dump ())
 
  (** @return l2 \ l1 *)
let uri_list_diff l2 l1 =
  let module S = UriManager.UriSet in
  let s1 = List.fold_left (fun set uri -> S.add uri set) S.empty l1 in
  let s2 = List.fold_left (fun set uri -> S.add uri set) S.empty l2 in
  let diff = S.diff s2 s1 in
  S.fold (fun uri uris -> uri :: uris) diff []

let initial_status lexicon_status baseuri =
 (new GrafiteTypes.status baseuri)#set_lstatus lexicon_status#lstatus
;;

let time_travel  ~present ?(past=initial_status present present#baseuri) () =
  let objs_to_remove =
   uri_list_diff present#objects past#objects in
  List.iter LibrarySync.remove_obj objs_to_remove;
  CoercDb.restore past#coercions;
  NCicLibrary.time_travel past
;;

let init lexicon_status =
  CoercDb.restore CoercDb.empty_coerc_db;
  LibraryObjects.reset_defaults ();
  initial_status lexicon_status
  ;;
let pop () =
  LibrarySync.pop ();
  LibraryObjects.pop ()
;;

let push () =
  LibrarySync.push ();
  LibraryObjects.push ()
;;

