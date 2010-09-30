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

type auto_params = Cic.term list option * (string * string) list 

val auto_tac:
  dbd:HSql.dbd -> 
  params:auto_params ->
  automation_cache:AutomationCache.cache ->
  ProofEngineTypes.tactic

val applyS_tac:
  dbd:HSql.dbd -> 
  term: Cic.term -> 
  params:auto_params ->
  automation_cache:AutomationCache.cache ->
  ProofEngineTypes.tactic

val demodulate_tac : 
  dbd:HSql.dbd -> 
  params:auto_params ->
  automation_cache:AutomationCache.cache ->
  ProofEngineTypes.tactic

val demodulate_theorem : 
  automation_cache:AutomationCache.cache -> 
  UriManager.uri -> 
  Cic.term * Cic.term

type auto_status = 
  Cic.context * 
  (* or list: goalno, goaltype, grey, depth, candidates: (goalno, c) *)
  (int * Cic.term * bool * int * (int * Cic.term Lazy.t) list) list * 
  (* and list *)
  (int * Cic.term * int) list *
  (* last moves *)
  Cic.term Lazy.t list

val get_auto_status : unit -> auto_status
val pause: bool -> unit
val step : unit -> unit
val give_hint : int -> unit
val give_prune_hint : int -> unit

val lambda_close : 
  ?prefix_name:string -> Cic.term -> Cic.metasenv -> Cic.context -> Cic.term *
  int

val pp_proofterm: Cic.term -> string 
val revision : string (* svn revision *)
val size_and_depth : Cic.context -> Cic.metasenv -> Cic.term -> int * int
