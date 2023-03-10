(* Copyright (C) 2019, HELM Team.
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

type just = [ `Term of NTacStatus.tactic_term | `Auto of NnAuto.auto_params ]

val assume : string -> NTacStatus.tactic_term -> 's NTacStatus.tactic
val suppose : NTacStatus.tactic_term -> string -> 's NTacStatus.tactic
val we_need_to_prove : NTacStatus.tactic_term -> string option -> 's NTacStatus.tactic
val beta_rewriting_step : NTacStatus.tactic_term -> 's NTacStatus.tactic
val bydone : just -> 's NTacStatus.tactic
val by_just_we_proved : just -> NTacStatus.tactic_term -> string option -> 's NTacStatus.tactic
val andelim : just -> NTacStatus.tactic_term -> string -> NTacStatus.tactic_term -> string -> 's
NTacStatus.tactic
val existselim : just -> string -> NTacStatus.tactic_term -> NTacStatus.tactic_term -> string -> 's
NTacStatus.tactic
val thesisbecomes : NTacStatus.tactic_term -> 's NTacStatus.tactic
val rewritingstep : NTacStatus.tactic_term -> [ `Term of NTacStatus.tactic_term | `Auto of NnAuto.auto_params
   | `Proof  | `SolveWith of NTacStatus.tactic_term ] ->
    bool (* last step *) -> 's NTacStatus.tactic
val we_proceed_by_cases_on: NTacStatus.tactic_term -> NTacStatus.tactic_term -> 's NTacStatus.tactic
val we_proceed_by_induction_on: NTacStatus.tactic_term -> NTacStatus.tactic_term -> 's NTacStatus.tactic
val byinduction: NTacStatus.tactic_term -> string -> 's NTacStatus.tactic
val case: string -> (string*NotationPt.term) list -> 's NTacStatus.tactic
val obtain: string -> NTacStatus.tactic_term -> 's NTacStatus.tactic
val conclude: NTacStatus.tactic_term -> 's NTacStatus.tactic
val print_stack : 's NTacStatus.tactic
