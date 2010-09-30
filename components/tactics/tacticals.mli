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

type tactic = ProofEngineTypes.tactic

val id_tac : tactic
val fail_tac: tactic

val first: tactics: tactic list -> tactic
val thens: start: tactic -> continuations: tactic list -> tactic
val then_: start: tactic -> continuation: tactic -> tactic
val ifs: start: tactic -> continuations: tactic list -> fail: tactic -> tactic
val if_: start: tactic -> continuation: tactic -> fail: tactic -> tactic
val seq: tactics: tactic list -> tactic (** "folding" of then_ *)
val repeat_tactic: tactic: tactic -> tactic
val do_tactic: n: int -> tactic: tactic -> tactic 
val try_tactic: tactic: tactic -> tactic 
val solve_tactics: tactics: tactic list -> tactic
val progress_tactic: tactic: tactic -> tactic 

(* TODO temporary *)
val goals_diff:
  before:ProofEngineTypes.goal list ->
  after:ProofEngineTypes.goal list ->
  opened:ProofEngineTypes.goal list ->
    ProofEngineTypes.goal list * ProofEngineTypes.goal list
