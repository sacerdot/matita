(* Copyright (C) 2002, HELM Team.
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

  (**
    current proof (proof uri * metas * (in)complete proof * term to be prooved)
  *)
type proof =
 UriManager.uri option * Cic.metasenv * Cic.substitution * Cic.term Lazy.t * Cic.term * Cic.attribute list
  (** current goal, integer index *)
type goal = int
type status = proof * goal

  (** @param goal
  * @param goal's metasenv
  * @return initial proof status for the given goal *)
val initial_status: Cic.term -> Cic.metasenv -> Cic.attribute list -> status

  (**
    a tactic: make a transition from one status to another one or, usually,
    raise a "Fail" (@see Fail) exception in case of failure
  *)
  (** an unfinished proof with the optional current goal *)
type tactic 
val mk_tactic: (status -> proof * goal list) -> tactic

type reduction = Cic.context -> Cic.term -> Cic.term

val const_lazy_term: Cic.term -> Cic.lazy_term

type lazy_reduction =
  Cic.context -> Cic.metasenv -> CicUniv.universe_graph ->
    reduction * Cic.metasenv * CicUniv.universe_graph

val const_lazy_reduction: reduction -> lazy_reduction

 (** what, hypothesis patterns, conclusion pattern *)
type ('term, 'lazy_term) pattern =
  'lazy_term option * (string * 'term) list * 'term option

type lazy_pattern = (Cic.term, Cic.lazy_term) pattern

 (** conclusion_pattern [t] returns the pattern (t,[],%) *)
val conclusion_pattern : Cic.term option -> lazy_pattern

  (** tactic failure *)
exception Fail of string Lazy.t

val apply_tactic: tactic -> status ->  proof * goal list
  
  (** constraint: the returned value will always be constructed by Cic.Name **)
type mk_fresh_name_type =
 Cic.metasenv -> Cic.context -> Cic.name -> typ:Cic.term -> Cic.name

val goals_of_proof: proof -> goal list

val hole: Cic.term
