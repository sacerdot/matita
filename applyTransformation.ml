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

module G = GrafiteAst

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

let txt_of_cic_sequent ~map_unicode_to_tex size metasenv sequent =
  let unsh_sequent,(asequent,ids_to_terms,
    ids_to_father_ids,ids_to_inner_sorts,ids_to_hypotheses)
  =
    Cic2acic.asequent_of_sequent metasenv sequent
  in
  let content_sequent = Acic2content.map_sequent asequent in 
  let pres_sequent = 
   CicNotationPres.mpres_of_box
    (Sequent2pres.sequent2pres ~ids_to_inner_sorts content_sequent)
  in
  BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size pres_sequent

let txt_of_cic_sequent_conclusion ~map_unicode_to_tex ~output_type size
 metasenv sequent =
  let _,(asequent,_,_,ids_to_inner_sorts,_) = 
    Cic2acic.asequent_of_sequent metasenv sequent 
  in
  let _,_,_,t = Acic2content.map_sequent asequent in 
  let t, ids_to_uris =
   TermAcicContent.ast_of_acic ~output_type ids_to_inner_sorts t in
  let t = TermContentPres.pp_ast t in
  let t = CicNotationPres.render ids_to_uris t in
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
         CicNotationPres.render ~prec:90 ids_to_uris 
            (TermContentPres.pp_ast ast)) in
   let render = function _::x::_ -> x | _ -> assert false in
   let mpres = CicNotationPres.mpres_of_box bobj in
   let s = BoxPp.render_to_string ~map_unicode_to_tex render n mpres in
   remove_closed_substs s

let txt_of_cic_object 
 ~map_unicode_to_tex ?skip_thm_and_qed ?skip_initial_lambdas n style prefix obj 
=
  let get_aobj obj = 
     try   
        let aobj,_,_,ids_to_inner_sorts,ids_to_inner_types,_,_ =
            Cic2acic.acic_object_of_cic_object obj
        in
        aobj, ids_to_inner_sorts, ids_to_inner_types
     with e -> 
        let msg = "txt_of_cic_object: " ^ Printexc.to_string e in
        failwith msg
  in
  match style with
     | G.Declarative      ->
        let aobj, ids_to_inner_sorts, ids_to_inner_types = get_aobj obj in
        let cobj = 
          Acic2content.annobj2content 
            ids_to_inner_sorts ids_to_inner_types aobj 
        in
        let bobj = 
          Content2pres.content2pres 
            ?skip_initial_lambdas ?skip_thm_and_qed ~ids_to_inner_sorts cobj 
        in
        remove_closed_substs ("\n\n" ^
           BoxPp.render_to_string ~map_unicode_to_tex
            (function _::x::_ -> x | _ -> assert false) n
            (CicNotationPres.mpres_of_box bobj)
        )
     | G.Procedural depth ->
        let obj = ProceduralOptimizer.optimize_obj obj in
        let aobj, ids_to_inner_sorts, ids_to_inner_types = get_aobj obj in
        let term_pp = term2pres ~map_unicode_to_tex (n - 8) ids_to_inner_sorts in
        let lazy_term_pp = term_pp in
        let obj_pp = CicNotationPp.pp_obj term_pp in
        let aux = GrafiteAstPp.pp_statement
         ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~obj_pp in
        let script = 
    Acic2Procedural.acic2procedural 
           ~ids_to_inner_sorts ~ids_to_inner_types ?depth ?skip_thm_and_qed prefix aobj 
  in
        String.concat "" (List.map aux script) ^ "\n\n"

let txt_of_inline_macro ~map_unicode_to_tex style suri prefix =
   let print_exc = function
      | ProofEngineHelpers.Bad_pattern s as e ->
           Printexc.to_string e ^ " " ^ Lazy.force s
      | e -> Printexc.to_string e
   in
   let dbd = LibraryDb.instance () in   
   let sorted_uris = MetadataDeps.sorted_uris_of_baseuri ~dbd suri in
   let map uri =
      try 
        txt_of_cic_object 
          ~map_unicode_to_tex 78 style prefix
          (fst (CicEnvironment.get_obj CicUniv.empty_ugraph uri))
      with
         | e -> 
            Printf.sprintf "\n(* ERRORE IN STAMPA DI %s\nEXCEPTION: %s *)\n" 
            (UriManager.string_of_uri uri) (print_exc e)
   in
   String.concat "" (List.map map sorted_uris)
