(* Copyright (C) 2000, HELM Team.
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

exception NotEnoughElements of string

val source_id_of_id : string -> string

type anntypes =
 {annsynthesized : Cic.annterm ; annexpected : Cic.annterm option}
;;

type sort_kind = [ `Prop | `Set | `Type of CicUniv.universe | `CProp of CicUniv.universe | `NType of string | `NCProp of string]

val string_of_sort: sort_kind -> string
(*val sort_of_string: string -> sort_kind*)
val sort_of_sort: Cic.sort -> sort_kind

val acic_object_of_cic_object :
  ?eta_fix: bool ->                       (* perform eta_fixing; default: true*)
  Cic.obj ->                              (* object *)
   Cic.annobj *                            (* annotated object *)
    (Cic.id, Cic.term) Hashtbl.t *         (* ids_to_terms *)
    (Cic.id, Cic.id option) Hashtbl.t *    (* ids_to_father_ids *)
    (Cic.id, sort_kind) Hashtbl.t *        (* ids_to_inner_sorts *)
    (Cic.id, anntypes) Hashtbl.t *         (* ids_to_inner_types *)
    (Cic.id, Cic.conjecture) Hashtbl.t *   (* ids_to_conjectures *)
    (Cic.id, Cic.hypothesis) Hashtbl.t     (* ids_to_hypotheses *)

val asequent_of_sequent :
  Cic.metasenv ->                         (* metasenv *)
   Cic.conjecture ->                      (* sequent *)
    Cic.conjecture *                       (* unshared sequent *)
    (Cic.annconjecture *                   (* annotated sequent *)
    (Cic.id, Cic.term) Hashtbl.t *         (* ids_to_terms *)
    (Cic.id, Cic.id option) Hashtbl.t *    (* ids_to_father_ids *)
    (Cic.id, sort_kind) Hashtbl.t *        (* ids_to_inner_sorts *)
    (Cic.id, Cic.hypothesis) Hashtbl.t)    (* ids_to_hypotheses *)

val plain_acic_object_of_cic_object : Cic.obj -> Cic.annobj

val acic_term_of_cic_term :
  ?eta_fix: bool ->                       (* perform eta_fixing; default: true*)
  Cic.context -> Cic.term ->               (* term and context *)
   Cic.annterm *                            (* annotated term *)
    (Cic.id, sort_kind) Hashtbl.t *         (* ids_to_inner_sorts *)
    (Cic.id, anntypes) Hashtbl.t            (* ids_to_inner_types *)
