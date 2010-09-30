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

val fresh_name: unit -> string

val variables_of_term: CicNotationPt.term -> CicNotationPt.pattern_variable list
val names_of_term: CicNotationPt.term -> string list

  (** extract all keywords (i.e. string literals) from a level 1 pattern *)
val keywords_of_term: CicNotationPt.term -> string list

val visit_ast:
  ?special_k:(CicNotationPt.term -> CicNotationPt.term) ->
  ?map_xref_option:(CicNotationPt.href option -> CicNotationPt.href option) ->
  ?map_case_indty:(CicNotationPt.case_indtype option ->
          CicNotationPt.case_indtype option) ->
  ?map_case_outtype:((CicNotationPt.term -> CicNotationPt.term) -> 
                     CicNotationPt.term option -> CicNotationPt.term
  option) ->
  (CicNotationPt.term -> CicNotationPt.term) ->
  CicNotationPt.term ->
    CicNotationPt.term

val visit_layout:
  (CicNotationPt.term -> CicNotationPt.term) ->
  CicNotationPt.layout_pattern ->
    CicNotationPt.layout_pattern

val visit_magic:
  (CicNotationPt.term -> CicNotationPt.term) ->
  CicNotationPt.magic_term ->
    CicNotationPt.magic_term

val visit_variable:
  (CicNotationPt.term -> CicNotationPt.term) ->
  CicNotationPt.pattern_variable ->
    CicNotationPt.pattern_variable

val strip_attributes: CicNotationPt.term -> CicNotationPt.term

  (** @return the list of proper (i.e. non recursive) IdRef of a term *)
val get_idrefs: CicNotationPt.term -> string list

  (** generalization of List.combine to n lists *)
val ncombine: 'a list list -> 'a list list

val string_of_literal: CicNotationPt.literal -> string

val dress:  sep:'a -> 'a list -> 'a list
val dressn: sep:'a list -> 'a list -> 'a list

val boxify: CicNotationPt.term list -> CicNotationPt.term
val group: CicNotationPt.term list -> CicNotationPt.term
val ungroup: CicNotationPt.term list -> CicNotationPt.term list

val find_appl_pattern_uris:
  CicNotationPt.cic_appl_pattern ->
   [`Uri of UriManager.uri | `NRef of NReference.reference] list

val find_branch:
  CicNotationPt.term -> CicNotationPt.term

val cic_name_of_name: CicNotationPt.term -> Cic.name
val name_of_cic_name: Cic.name -> CicNotationPt.term

  (** Symbol/Numbers instances *)

val freshen_term: CicNotationPt.term -> CicNotationPt.term
val freshen_obj: CicNotationPt.term CicNotationPt.obj -> CicNotationPt.term CicNotationPt.obj

  (** Notation id handling *)

type notation_id

val fresh_id: unit -> notation_id

