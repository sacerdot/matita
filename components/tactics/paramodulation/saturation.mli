(* Copyright (C) 2006, HELM Team.
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

(* $Id$ *)

type passive_table
type active_table = Equality.equality list * Indexing.Index.t

val reset_refs : unit -> unit

val make_active: Equality.equality list -> active_table
val make_passive: Equality.equality list -> passive_table
val add_to_passive: Equality.equality list -> passive_table -> passive_table
val add_to_active: 
      Equality.equality_bag -> 
      active_table -> passive_table ->
      Utils.environment -> Cic.term (* ty *) -> Cic.term -> Cic.metasenv ->
          active_table * passive_table * Equality.equality_bag 
val list_of_passive: passive_table -> Equality.equality list
val list_of_active: active_table -> Equality.equality list

val simplify_equalities : 
  Equality.equality_bag ->
  UriManager.uri ->
  Utils.environment -> 
  Equality.equality list -> 
  Equality.equality_bag * Equality.equality list
val pump_actives :
  Cic.context ->
  Equality.equality_bag ->
  active_table ->
  passive_table -> 
  int -> 
  float -> 
  active_table * passive_table * Equality.equality_bag
val all_subsumed :
  Equality.equality_bag ->
  ProofEngineTypes.status ->
  active_table ->
  passive_table -> 
  (Cic.substitution * 
     ProofEngineTypes.proof * 
     ProofEngineTypes.goal list) list
val given_clause: 
  Equality.equality_bag ->
  ProofEngineTypes.status ->
  active_table ->
  passive_table -> 
  int -> int -> float -> 
    (Cic.substitution * 
     ProofEngineTypes.proof * 
     ProofEngineTypes.goal list) option * 
    active_table * passive_table * Equality.equality_bag

val solve_narrowing: 
  Equality.equality_bag ->
  ProofEngineTypes.status ->
  active_table ->
  passive_table -> 
  int -> 
    (Cic.substitution * 
     ProofEngineTypes.proof * 
     ProofEngineTypes.goal list) option * 
    active_table * passive_table * Equality.equality_bag
