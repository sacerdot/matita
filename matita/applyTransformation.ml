(* Copyright (C) 2000-2002, HELM Team.
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

(***************************************************************************)
(*                                                                         *)
(*                               PROJECT HELM                              *)
(*                                                                         *)
(*                   Andrea Asperti <asperti@cs.unibo.it>                  *)
(*                                21/11/2003                               *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)

(* $Id$ *)

module UM = UriManager
module C  = Cic
module Un = CicUniv
module E  = CicEnvironment
module TC = CicTypeChecker
module G  = GrafiteAst
module GE = GrafiteEngine
module LS = LibrarySync
module Ds = CicDischarge
module N = CicNotationPt

let mpres_document pres_box =
  Xml.add_xml_declaration (CicNotationPres.print_box pres_box)

let mml_of_cic_sequent metasenv sequent =
  let unsh_sequent,(asequent,ids_to_terms,
    ids_to_father_ids,ids_to_inner_sorts,ids_to_hypotheses)
  =
    Cic2acic.asequent_of_sequent metasenv sequent
  in
  let content_sequent = Acic2content.map_sequent asequent in 
  let pres_sequent = 
   Sequent2pres.sequent2pres ~ids_to_inner_sorts content_sequent in
  let xmlpres = mpres_document pres_sequent in
  (Xml2Gdome.document_of_xml DomMisc.domImpl xmlpres,
   unsh_sequent,
   (asequent,
    (ids_to_terms,ids_to_father_ids,ids_to_hypotheses,ids_to_inner_sorts)))

let nmml_of_cic_sequent status metasenv subst sequent =
  let content_sequent,ids_to_refs =
   NTermCicContent.nmap_sequent status ~metasenv ~subst sequent in 
  let pres_sequent = 
   Sequent2pres.nsequent2pres ids_to_refs subst content_sequent in
  let xmlpres = mpres_document pres_sequent in
   Xml2Gdome.document_of_xml DomMisc.domImpl xmlpres

let ntxt_of_cic_sequent ~map_unicode_to_tex size status metasenv subst sequent =
  let content_sequent,ids_to_refs =
   NTermCicContent.nmap_sequent status ~metasenv ~subst sequent in 
  let pres_sequent = 
   Sequent2pres.nsequent2pres ids_to_refs subst content_sequent in
  let pres_sequent = CicNotationPres.mpres_of_box pres_sequent in
   BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size pres_sequent

let mml_of_cic_object obj =
  let (annobj, ids_to_terms, ids_to_father_ids, ids_to_inner_sorts,
    ids_to_inner_types, ids_to_conjectures, ids_to_hypotheses)
  =
    Cic2acic.acic_object_of_cic_object obj
  in
  let content = 
    Acic2content.annobj2content ~ids_to_inner_sorts ~ids_to_inner_types annobj
  in
  let pres = Content2pres.content2pres ~ids_to_inner_sorts content in
  let xmlpres = mpres_document pres in
  let mathml = Xml2Gdome.document_of_xml DomMisc.domImpl xmlpres in
  (mathml,(annobj,
   (ids_to_terms, ids_to_father_ids, ids_to_conjectures, ids_to_hypotheses,
  ids_to_inner_sorts,ids_to_inner_types)))

let nmml_of_cic_object status obj =
 let cobj,ids_to_nrefs = NTermCicContent.nmap_obj status obj in 
 let pres_sequent = Content2pres.ncontent2pres ~ids_to_nrefs cobj in
 let xmlpres = mpres_document pres_sequent in
  Xml2Gdome.document_of_xml DomMisc.domImpl xmlpres
;;

let ntxt_of_cic_object ~map_unicode_to_tex size status obj =
 let cobj,ids_to_nrefs = NTermCicContent.nmap_obj status obj in 
 let pres_sequent = Content2pres.ncontent2pres ~ids_to_nrefs cobj in
 let pres_sequent = CicNotationPres.mpres_of_box pres_sequent in
  BoxPp.render_to_string ~map_unicode_to_tex
   (function x::_ -> x | _ -> assert false) size pres_sequent
;;

let txt_of_cic_sequent_all ~map_unicode_to_tex size metasenv sequent =
  let unsh_sequent,(asequent,ids_to_terms,
    ids_to_father_ids,ids_to_inner_sorts,ids_to_hypotheses)
  =
    Cic2acic.asequent_of_sequent metasenv sequent
  in
  let content_sequent = Acic2content.map_sequent asequent in 
  let pres_sequent = 
   CicNotationPres.mpres_of_box
    (Sequent2pres.sequent2pres ~ids_to_inner_sorts content_sequent) in
  let txt =
  BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size pres_sequent
  in
  (txt,
   unsh_sequent,
   (asequent,
    (ids_to_terms,ids_to_father_ids,ids_to_hypotheses,ids_to_inner_sorts)))

let txt_of_cic_sequent ~map_unicode_to_tex size metasenv sequent =
 let txt,_,_ = txt_of_cic_sequent_all ~map_unicode_to_tex size metasenv sequent
 in txt
;;

let txt_of_cic_sequent_conclusion ~map_unicode_to_tex ~output_type size
 metasenv sequent =
  let _,(asequent,_,_,ids_to_inner_sorts,_) = 
    Cic2acic.asequent_of_sequent metasenv sequent 
  in
  let _,_,_,t = Acic2content.map_sequent asequent in 
  let t, ids_to_uris =
   TermAcicContent.ast_of_acic ~output_type ids_to_inner_sorts t in
  let t = TermContentPres.pp_ast t in
  let t =
   CicNotationPres.render ~lookup_uri:(CicNotationPres.lookup_uri ids_to_uris) t
  in
   BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size t

let txt_of_cic_term ~map_unicode_to_tex size metasenv context t = 
 let fake_sequent = (-1,context,t) in
  txt_of_cic_sequent_conclusion ~map_unicode_to_tex ~output_type:`Term size
   metasenv fake_sequent 
;;

ignore (
 CicMetaSubst.set_ppterm_in_context
  (fun ~metasenv subst term context ->
    try
     let context' = CicMetaSubst.apply_subst_context subst context in
     let metasenv = CicMetaSubst.apply_subst_metasenv subst metasenv in
     let term' = CicMetaSubst.apply_subst subst term in
     let res =
      txt_of_cic_term
       ~map_unicode_to_tex:(Helm_registry.get_bool "matita.paste_unicode_as_tex")
       30 metasenv context' term' in
      if String.contains res '\n' then
       "\n" ^ res ^ "\n"
      else
       res
    with
       Sys.Break as exn -> raise exn
     | exn ->
        "[[ Exception raised during pretty-printing: " ^
         (try
           Printexc.to_string exn
          with
             Sys.Break as exn -> raise exn
           | _ -> "<<exception raised pretty-printing the exception>>"
         ) ^ " ]] " ^
        (CicMetaSubst.use_low_level_ppterm_in_context := true;
         try
          let res =
           CicMetaSubst.ppterm_in_context ~metasenv subst term context
          in
           CicMetaSubst.use_low_level_ppterm_in_context := false;
           res
         with
          exc -> 
           CicMetaSubst.use_low_level_ppterm_in_context := false;
           raise exc))
);;

(****************************************************************************)
(* txt_of_cic_object: IMPROVE ME *)

let remove_closed_substs s =
    Pcre.replace ~pat:"{...}" ~templ:"" s

let term2pres ~map_unicode_to_tex n ids_to_inner_sorts annterm = 
   let ast, ids_to_uris = 
    TermAcicContent.ast_of_acic ~output_type:`Term ids_to_inner_sorts annterm in
   let bobj =
    CicNotationPres.box_of_mpres (
     CicNotationPres.render ~prec:90
      ~lookup_uri:(CicNotationPres.lookup_uri ids_to_uris)
      (TermContentPres.pp_ast ast)) in
   let render = function _::x::_ -> x | _ -> assert false in
   let mpres = CicNotationPres.mpres_of_box bobj in
   let s = BoxPp.render_to_string ~map_unicode_to_tex render n mpres in
   remove_closed_substs s

let enable_notations = function
   | true -> 
      CicNotation.set_active_notations
         (List.map fst (CicNotation.get_all_notations ()))
   | false ->
      CicNotation.set_active_notations []

let txt_of_cic_object_all
 ~map_unicode_to_tex ?skip_thm_and_qed ?skip_initial_lambdas n params obj 
=
  let get_aobj obj = 
     try   
        let
          aobj,ids_to_terms,ids_to_father_ids,ids_to_inner_sorts,ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses =
            Cic2acic.acic_object_of_cic_object obj
        in
        aobj, ids_to_terms, ids_to_father_ids, ids_to_inner_sorts,
        ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses
     with 
        | E.Object_not_found uri -> 
             let msg = "txt_of_cic_object: object not found: " ^ UM.string_of_uri uri in
             failwith msg
	| e                     ->
             let msg = "txt_of_cic_object: " ^ Printexc.to_string e in
             failwith msg
  in
  (*MATITA1.0
  if List.mem G.IPProcedural params then begin

     Procedural2.debug := A2P.is_debug 1 params;
     PO.debug := A2P.is_debug 2 params;
(*     
     PO.critical := false;
     A2P.tex_formatter := Some Format.std_formatter;	
     let _ = ProceduralTeX.tex_of_obj Format.std_formatter obj in
*)	
     let obj, info = PO.optimize_obj obj in
(*	
     let _ = ProceduralTeX.tex_of_obj Format.std_formatter obj in
*)	
     let  aobj, ids_to_terms, ids_to_father_ids, ids_to_inner_sorts,
       ids_to_inner_types,ids_to_conjectures,ids_to_hypothesis = get_aobj obj in
     let term_pp = term2pres ~map_unicode_to_tex (n - 8) ids_to_inner_sorts in
     let lazy_term_pp = term_pp in
     let obj_pp = CicNotationPp.pp_obj term_pp in
     let stm_pp = 	      
	GrafiteAstPp.pp_statement
	   ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~obj_pp
     in
     let aux = function
	| G.Executable (_, G.Command (_, G.Obj (_, N.Inductive _)))
	| G.Executable (_, G.Command (_, G.Obj (_, N.Record _))) as stm
	      -> 	   
	   let hc = !Acic2content.hide_coercions in
	   if List.mem G.IPCoercions params then 
	      Acic2content.hide_coercions := false;
	   enable_notations false;
	   let str = stm_pp stm in 
	   enable_notations true;
	   Acic2content.hide_coercions := hc;
	   str
(* FG: we disable notation for inductive types to avoid recursive notation *) 
	| G.Executable (_, G.Tactic _) as stm -> 
	   let hc = !Acic2content.hide_coercions in
	   Acic2content.hide_coercions := false;
	   let str = stm_pp stm in
	   Acic2content.hide_coercions := hc;
           str
(* FG: we show coercion because the reconstruction is not aware of them *)
	| stm -> 
	   let hc = !Acic2content.hide_coercions in
	   if List.mem G.IPCoercions params then 
	      Acic2content.hide_coercions := false;
	   let str = stm_pp stm in
	   Acic2content.hide_coercions := hc;
           str
     in
     let script = 
        A2P.procedural_of_acic_object 
           ~ids_to_inner_sorts ~ids_to_inner_types ~info params aobj 
     in
     String.concat "" (List.map aux script) ^ "\n\n"
  end else *)
     let  aobj, ids_to_terms, ids_to_father_ids, ids_to_inner_sorts,
       ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses = get_aobj obj in
     let cobj = 
       Acic2content.annobj2content ids_to_inner_sorts ids_to_inner_types aobj 
     in
     let bobj = 
        Content2pres.content2pres 
           ?skip_initial_lambdas ?skip_thm_and_qed ~ids_to_inner_sorts cobj 
     in
     let txt =
      remove_closed_substs (
        BoxPp.render_to_string ~map_unicode_to_tex
           (function _::x::_ -> x | _ -> assert false) n
           (CicNotationPres.mpres_of_box bobj)
        ^ "\n\n"
      )
     in
      (txt,(aobj,
       (ids_to_terms, ids_to_father_ids, ids_to_conjectures, ids_to_hypotheses,
      ids_to_inner_sorts,ids_to_inner_types)))

let txt_of_cic_object
 ~map_unicode_to_tex ?skip_thm_and_qed ?skip_initial_lambdas n params obj 
=
 let txt,_ = txt_of_cic_object_all
  ~map_unicode_to_tex ?skip_thm_and_qed ?skip_initial_lambdas n params obj
 in txt

let cic_prefix = Str.regexp_string "cic:/"
let matita_prefix = Str.regexp_string "cic:/matita/"
let suffixes = [".ind"; "_rec.con"; "_rect.con"; "_ind.con"; ".con"]

let replacements = 
   let map s = String.length s, s, Str.regexp_string s, "_discharged" ^ s in 
   List.map map suffixes

let replacement (ok, u) (l, s, x, t) =
   if ok then ok, u else
   if Str.last_chars u l = s then true, Str.replace_first x t u else ok, u

let discharge_uri params uri =
   let template = 
      if List.mem G.IPProcedural params then "cic:/matita/procedural/"
      else "cic:/matita/declarative/"
   in
   let s = UM.string_of_uri uri in
   if Str.string_match matita_prefix s 0 then uri else
   let s = Str.replace_first cic_prefix template s in
   let _, s = List.fold_left replacement (false, s) replacements in 
   UM.uri_of_string s

let discharge_name s = s ^ "_discharged"

let txt_of_inline_uri ~map_unicode_to_tex params suri =
(*   
   Ds.debug := true;
*)
   let print_exc = Printexc.to_string in
   let dbd = LibraryDb.instance () in   
   let sorted_uris = MetadataDeps.sorted_uris_of_baseuri ~dbd suri in
   let error uri e =
      let msg  = 
         Printf.sprintf 
            "ERROR IN THE GENERATION OF %s\nEXCEPTION: %s" 
            (UM.string_of_uri uri) e
      in
      Printf.eprintf "%s\n" msg;
      GrafiteTypes.command_error msg
   in
   let map uri =
      Librarian.time_stamp "AT: BEGIN MAP";
      try
(* FG: for now the explicit variables must be discharged *)
        let do_it obj =
	   let r = txt_of_cic_object ~map_unicode_to_tex 78 params obj in
	   Librarian.time_stamp "AT: END MAP  "; r
	in
	let obj, real = 
	   let s = UM.string_of_uri uri in
	   if Str.string_match matita_prefix s 0 then begin
	      Librarian.time_stamp "AT: GETTING OBJECT";
	      let obj, _ = E.get_obj Un.default_ugraph uri in
	      Librarian.time_stamp "AT: DONE          ";
              obj, true
	   end else
	      Ds.discharge_uri discharge_name (discharge_uri params) uri
	in
	if real then do_it obj else
	let newuri = discharge_uri params uri in
	let _lemmas = LS.add_obj ~pack_coercion_obj:CicRefine.pack_coercion_obj newuri obj in
	do_it obj
      with
         | TC.TypeCheckerFailure s ->
	    error uri ("failure  : " ^ Lazy.force s)
         | TC.AssertFailure s      ->
	    error uri ("assert   : " ^ Lazy.force s)
         | E.Object_not_found u    ->
	    error uri ("not found: " ^ UM.string_of_uri u)
	 | e                       -> error uri (print_exc e)
   in
   String.concat "" (List.map map sorted_uris)

let txt_of_inline_macro ~map_unicode_to_tex params name =
   let suri = 
      if Librarian.is_uri name then name else
      let include_paths = 
         Helm_registry.get_list Helm_registry.string "matita.includes"
      in
      let _, baseuri, _, _ = 
         Librarian.baseuri_of_script ~include_paths name
      in
      baseuri ^ "/"
   in
   txt_of_inline_uri ~map_unicode_to_tex params suri

let txt_of_macro ~map_unicode_to_tex metasenv context m =
   GrafiteAstPp.pp_macro
     ~term_pp:(txt_of_cic_term ~map_unicode_to_tex 80 metasenv context) 
     ~lazy_term_pp:(fun (f : Cic.lazy_term) ->
        let t,metasenv,_ = f context metasenv CicUniv.empty_ugraph in
        txt_of_cic_term ~map_unicode_to_tex 80 metasenv context t)
     m
;;


