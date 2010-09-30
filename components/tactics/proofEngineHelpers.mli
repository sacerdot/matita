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

exception Bad_pattern of string Lazy.t

(* Returns the first meta whose number is above the *)
(* number of the higher meta.                       *)
val new_meta_of_proof : proof:ProofEngineTypes.proof -> int

val subst_meta_in_proof :
  ProofEngineTypes.proof ->
  int -> Cic.term -> Cic.metasenv ->
  ProofEngineTypes.proof * Cic.metasenv
val subst_meta_and_metasenv_in_proof :
  ProofEngineTypes.proof ->
  int -> Cic.substitution -> Cic.metasenv ->
  ProofEngineTypes.proof * Cic.metasenv

(* returns the list of goals that are in newmetasenv and were not in
   oldmetasenv *)
val compare_metasenvs :
  oldmetasenv:Cic.metasenv -> newmetasenv:Cic.metasenv -> int list


(** { Patterns }
 * A pattern is a Cic term in which Cic.Implicit terms annotated with `Hole
 * appears *)

(** create a pattern from a term and a list of subterms.
* the pattern is granted to have a ? for every subterm that has no selected
* subterms
* @param equality equality function used while walking the term. Defaults to
* physical equality (==) *)
val pattern_of:
 ?equality:(Cic.term -> Cic.term -> bool) -> term:Cic.term -> Cic.term list ->
   Cic.term


(** select metasenv conjecture pattern
* select all subterms of [conjecture] matching [pattern].
* It returns the set of matched terms (that can be compared using physical
* equality to the subterms of [conjecture]) together with their contexts.
* The representation of the set mimics the conjecture type (but for the id):
* a list of (possibly removed) hypothesis (without their names) together with
* the list of its matched subterms (and their contexts) + the list of matched
* subterms of the conclusion with their context. Note: in the result the list
* of hypotheses * has an entry for each entry in the context and in the same
* order. Of course the list of terms (with their context) associated to one
* hypothesis may be empty. 
*
* @raise Bad_pattern
* *)
val select:
 metasenv:Cic.metasenv ->
 subst:Cic.substitution ->
 ugraph:CicUniv.universe_graph ->
 conjecture:Cic.conjecture ->
 pattern:ProofEngineTypes.lazy_pattern ->
  Cic.substitution * Cic.metasenv * CicUniv.universe_graph *
  [ `Decl of (Cic.context * Cic.term) list
  | `Def of (Cic.context * Cic.term) list * (Cic.context * Cic.term) list
  ] option list *
  (Cic.context * Cic.term) list

(** locate_in_term equality what where context
* [what] must match a subterm of [where] according to [equality]
* It returns the matched terms together with their contexts in [where]
* [equality] defaults to physical equality
* [context] must be the context of [where]
*)
val locate_in_term:
 ?equality:(Cic.context -> Cic.term -> Cic.term -> bool) ->
  Cic.term -> where:Cic.term -> Cic.context -> (Cic.context * Cic.term) list

(** locate_in_conjecture equality what where context
* [what] must match a subterm of [where] according to [equality]
* It returns the matched terms together with their contexts in [where]
* [equality] defaults to physical equality
* [context] must be the context of [where]
*)
val locate_in_conjecture:
 ?equality:(Cic.context -> Cic.term -> Cic.term -> bool) ->
  Cic.term -> Cic.conjecture -> (Cic.context * Cic.term) list

(* returns the index and the type of a premise in a context *)
val lookup_type: Cic.metasenv -> Cic.context -> string -> int * Cic.term

(* orders a metasenv w.r.t. dependency among metas *)
val sort_metasenv: Cic.metasenv -> Cic.metasenv

(* finds an hypothesis by name in the context *)
val find_hyp: string -> Cic.context -> Cic.term * Cic.term

(* sort pattern hypotheses from the smallest to the highest Rel *)
val sort_pattern_hyps:
 Cic.context -> ProofEngineTypes.lazy_pattern -> ProofEngineTypes.lazy_pattern


(* FG: some helper functions ************************************************)

val get_name: Cic.context -> int -> string option

val get_rel: Cic.context -> string -> Cic.term option

(* split_with_whd (c, t) takes a type t typed in the context c and returns
   [(c_0, t_0); (c_1, t_1); ...; (c_n, t_n)], n where t_0 is the conclusion of
   t and t_i is the premise of t accessed by Rel i in t_0. 
   Performes a whd on the conclusion before giving up.
   Each t_i is returned with a context c_i in wich it is typed
   split_with_normalize (c, t) normalizes t before operating the split
   whd is useless here
*)
val split_with_whd: Cic.context * Cic.term -> 
                    (Cic.context * Cic.term) list * int
val split_with_normalize: Cic.context * Cic.term -> 
                          (Cic.context * Cic.term) list * int
