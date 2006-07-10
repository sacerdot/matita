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
    (Sequent2pres.sequent2pres ~ids_to_inner_sorts content_sequent)
  in
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

let txt_of_cic_sequent_conclusion size metasenv sequent = 
  let _,(asequent,_,_,ids_to_inner_sorts,_) = 
    Cic2acic.asequent_of_sequent metasenv sequent 
  in
  let _,_,_,t = Acic2content.map_sequent asequent in 
  let t, ids_to_uris = TermAcicContent.ast_of_acic ids_to_inner_sorts t in
  let t = TermContentPres.pp_ast t in
  let t = CicNotationPres.render ids_to_uris t in
  BoxPp.render_to_string (function x::_ -> x | _ -> assert false) size t

let txt_of_cic_term size metasenv context t = 
  let fake_sequent = (-1,context,t) in
  txt_of_cic_sequent_conclusion size metasenv fake_sequent 

