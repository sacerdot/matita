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
 * http://cs.unibo.it/helm/.
 *)

type just = [ `Term of Cic.term | `Auto of Auto.auto_params ]

val assume : string -> Cic.term -> ProofEngineTypes.tactic

val suppose : Cic.term -> string -> Cic.term option -> ProofEngineTypes.tactic

val by_just_we_proved :
 dbd:HSql.dbd -> automation_cache:AutomationCache.cache -> 
 just -> Cic.term -> string option -> Cic.term option ->
 ProofEngineTypes.tactic

val bydone : dbd:HSql.dbd -> automation_cache:AutomationCache.cache ->
  just -> ProofEngineTypes.tactic

val we_need_to_prove :
 Cic.term -> string option -> Cic.term option -> ProofEngineTypes.tactic

val we_proceed_by_cases_on : Cic.term -> Cic.term -> ProofEngineTypes.tactic

val we_proceed_by_induction_on : Cic.term -> Cic.term -> ProofEngineTypes.tactic

val byinduction : Cic.term -> string -> ProofEngineTypes.tactic

val thesisbecomes : Cic.term -> ProofEngineTypes.tactic

val case : string -> params:(string * Cic.term) list -> ProofEngineTypes.tactic

val existselim :
  dbd:HSql.dbd -> automation_cache:AutomationCache.cache -> just ->
  string -> Cic.term -> string -> Cic.lazy_term -> ProofEngineTypes.tactic

val andelim :
 dbd:HSql.dbd -> automation_cache:AutomationCache.cache -> just ->
 string -> Cic.term -> string -> Cic.term -> ProofEngineTypes.tactic

val rewritingstep :
 dbd:HSql.dbd -> automation_cache:AutomationCache.cache ->
  (string option * Cic.term) option -> Cic.term ->
   [ `Term of Cic.term | `Auto of Auto.auto_params
   | `Proof  | `SolveWith of Cic.term] ->
    bool (* last step *) -> ProofEngineTypes.tactic
