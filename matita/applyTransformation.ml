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

let ntxt_of_cic_sequent ~map_unicode_to_tex size status metasenv subst sequent =
  let content_sequent,ids_to_refs =
   NTermCicContent.nmap_sequent status ~metasenv ~subst sequent in 
  let pres_sequent = 
   Sequent2pres.nsequent2pres ids_to_refs subst content_sequent in
  let pres_sequent = CicNotationPres.mpres_of_box pres_sequent in
   BoxPp.render_to_string ~map_unicode_to_tex
    (function x::_ -> x | _ -> assert false) size pres_sequent

let ntxt_of_cic_object ~map_unicode_to_tex size status obj =
 let cobj,ids_to_nrefs = NTermCicContent.nmap_obj status obj in 
 let pres_sequent = Content2pres.ncontent2pres ~ids_to_nrefs cobj in
 let pres_sequent = CicNotationPres.mpres_of_box pres_sequent in
  BoxPp.render_to_string ~map_unicode_to_tex
   (function x::_ -> x | _ -> assert false) size pres_sequent
;;
