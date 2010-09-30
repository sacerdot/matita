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

(**** useful only to implement tactics similar to apply ****)

val generalize_exp_named_subst_with_fresh_metas :
  Cic.context ->
  int ->
  UriManager.uri ->
  (UriManager.uri * Cic.term) list ->
  int * Cic.metasenv *
  Cic.term Cic.explicit_named_substitution *
  Cic.term Cic.explicit_named_substitution

val classify_metas :
  Cic.term ->
  (Cic.term -> bool) ->
  (Cic.context -> Cic.term -> Cic.term) ->
  (Cic.term * Cic.context * Cic.term) list ->
  (Cic.term * Cic.context * Cic.term) list *
  (Cic.term * Cic.context * Cic.term) list

(* Not primitive, but useful for elim *)

exception AllSelectedTermsMustBeConvertible;;

val generalize_tac:
 ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
 ProofEngineTypes.lazy_pattern ->
   ProofEngineTypes.tactic

(* not a real tactic *)
val apply_tac_verbose :
  term:Cic.term ->
  ProofEngineTypes.proof * int ->
  (Cic.term -> Cic.term) * (ProofEngineTypes.proof * int list)

(* the proof status has a subst now, and apply_tac honors it *)
val apply_tac:
  term: Cic.term -> ProofEngineTypes.tactic
val applyP_tac: (* apply for procedural reconstruction *)
  term: Cic.term -> ProofEngineTypes.tactic
val exact_tac:
  term: Cic.term -> ProofEngineTypes.tactic
val intros_tac:
  ?howmany:int ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type -> unit ->
   ProofEngineTypes.tactic
val cut_tac:
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  Cic.term ->
   ProofEngineTypes.tactic 
val letin_tac:
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  Cic.term ->
   ProofEngineTypes.tactic 

val elim_intros_simpl_tac:
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?depth:int -> ?using:Cic.term -> 
  ?pattern:ProofEngineTypes.lazy_pattern -> Cic.term ->
  ProofEngineTypes.tactic 
val elim_intros_tac:
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?depth:int -> ?using:Cic.term -> 
  ?pattern:ProofEngineTypes.lazy_pattern -> Cic.term ->
  ProofEngineTypes.tactic 

val cases_intros_tac:
  ?howmany:int ->
  ?mk_fresh_name_callback:ProofEngineTypes.mk_fresh_name_type ->
  ?pattern:ProofEngineTypes.lazy_pattern -> Cic.term ->
  ProofEngineTypes.tactic 

(* FG *)

val mk_predicate_for_elim: 
 context:Cic.context -> metasenv:Cic.metasenv -> subst:Cic.substitution ->
 ugraph:CicUniv.universe_graph -> goal:Cic.term -> 
 arg:Cic.term -> using:Cic.term -> cpattern:Cic.term -> args_no:int -> 
 Cic.metasenv * Cic.substitution * Cic.term * Cic.term * Cic.term list
