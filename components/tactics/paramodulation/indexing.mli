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

(* $Id$ *)

module Index :
  sig
    module PosEqSet : Set.S 
      with type elt = Utils.pos * Equality.equality
      and type t = Equality_indexing.DT.PosEqSet.t
    type t =
            Discrimination_tree.Make(Cic_indexable.CicIndexable)(PosEqSet).t
  end

val check_for_duplicates : Cic.metasenv -> string -> unit
val index : Index.t -> Equality.equality -> Index.t
val remove_index : Index.t -> Equality.equality -> Index.t
val in_index : Index.t -> Equality.equality -> bool
val empty : Index.t
val init_index : unit -> unit
val unification :
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality ->
  (Subst.substitution * Equality.equality * bool) option
val subsumption :
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality ->
  (Subst.substitution * Equality.equality * bool) option
val unification_all :
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality ->
  (Subst.substitution * Equality.equality * bool) list
val subsumption_all :
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality ->
  (Subst.substitution * Equality.equality * bool) list
val superposition_left :
  Equality.equality_bag ->
  Cic.conjecture list * Cic.context * CicUniv.universe_graph ->
  Index.t -> Equality.goal -> 
    Equality.equality_bag * Equality.goal list

val superposition_right :
  Equality.equality_bag ->
  ?subterms_only:bool ->
    UriManager.uri ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality ->
  Equality.equality_bag * Equality.equality list

val demod :
  Equality.equality_bag ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.goal ->
  bool * Equality.goal
val demodulation_equality :
  Equality.equality_bag ->
  ?from:string -> 
  UriManager.uri ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.equality -> Equality.equality_bag * Equality.equality
val demodulation_goal :
  Equality.equality_bag ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.goal ->
  bool * Equality.goal
val demodulation_all_goal :
  Equality.equality_bag ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.goal -> int ->
    Equality.goal list
val demodulation_theorem :
  Equality.equality_bag ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t -> 
  Cic.term * Cic.term * Cic.metasenv 
  -> Cic.term * Cic.term

val check_target:
  Equality.equality_bag ->
  Cic.context ->
    Equality.equality -> string -> unit
val solve_demodulating: 
  Equality.equality_bag ->
  Cic.metasenv * Cic.context * CicUniv.universe_graph ->
  Index.t ->
  Equality.goal ->
  int ->
    (Equality.equality_bag * Equality.goal_proof * Cic.metasenv * 
      Subst.substitution * Equality.proof) option

