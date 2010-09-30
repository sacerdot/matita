(* Copyright (C) 2005, HELM Team.
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

(* (weight of constants, [(meta, weight_of_meta)]) *)

val time : bool
val debug : bool
val debug_metas: bool
val debug_res: bool

type weight = int * (int * int) list;;

type comparison = Lt | Le | Eq | Ge | Gt | Incomparable;;

type environment = Cic.metasenv * Cic.context * CicUniv.universe_graph

val print_metasenv: Cic.metasenv -> string

val print_subst: ?prefix:string -> Cic.substitution -> string

val string_of_weight: weight -> string

val weight_of_term: 
  ?consider_metas:bool ->
  ?count_metas_occurrences:bool-> Cic.term -> weight

val normalize_weight: int -> weight -> weight

val string_of_comparison: comparison -> string

val compare_weights: ?normalize:bool -> weight -> weight -> comparison

val nonrec_kbo: Cic.term -> Cic.term -> comparison

val rpo: Cic.term -> Cic.term -> comparison

val nonrec_kbo_w: (Cic.term * weight) -> (Cic.term * weight) -> comparison

val names_of_context: Cic.context -> (Cic.name option) list

module TermMap: Map.S with type key = Cic.term

val symbols_of_term: Cic.term -> int TermMap.t
val set_goal_symbols: Cic.term -> unit

val lpo: Cic.term -> Cic.term -> comparison

val kbo: Cic.term -> Cic.term -> comparison

val ao: Cic.term -> Cic.term -> comparison

(** term-ordering function settable by the user *)
val compare_terms: (Cic.term -> Cic.term -> comparison) ref

val guarded_simpl:  ?debug:bool -> Cic.context -> Cic.term -> Cic.term

type pos = Left | Right 

val string_of_pos: pos -> string

val compute_equality_weight: Cic.term * Cic.term * Cic.term * comparison -> int

val debug_print: string Lazy.t -> unit

val metas_of_term: Cic.term -> int list

val remove_local_context: Cic.term -> Cic.term
