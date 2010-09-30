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

val simpl_tac: pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val whd_tac: pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val normalize_tac: pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic
val head_beta_reduce_tac: ?delta:bool -> ?upto:int -> pattern:ProofEngineTypes.lazy_pattern -> ProofEngineTypes.tactic

(* The default of term is the thesis of the goal to be prooved *)
val unfold_tac:
  Cic.lazy_term option ->
  pattern:ProofEngineTypes.lazy_pattern ->
    ProofEngineTypes.tactic

val change_tac: 
  ?with_cast:bool ->
  pattern:ProofEngineTypes.lazy_pattern ->
  Cic.lazy_term ->
    ProofEngineTypes.tactic 

val fold_tac:
 reduction:ProofEngineTypes.lazy_reduction ->
 term:Cic.lazy_term ->
 pattern:ProofEngineTypes.lazy_pattern ->
   ProofEngineTypes.tactic

