(* Copyright (C) 2004, HELM Team.
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

(** Stateful handling of proof status *)

exception No_goal_left
exception Uri_redefinition

type event = [ `Proof_changed | `Proof_completed ]

val all_events: event list

  (** from our point of view a status is the status of an incomplete proof, thus
  * we have an optional goal which is None if the proof is not yet completed
  * (i.e. some goal is still open) *)
type proof_status = ProofEngineTypes.proof * ProofEngineTypes.goal option

  (** Proof observer. First callback argument is Some extended_status
  * when a 'real 'change of the proof happened and None when Proof_changed event
  * was triggered by a time travel by the means of undo/redo actions or by an
  * external "#notify" invocation. Embedded status is the status _before_ the
  * current change. Second status is the status reached _after_ the current
  * change. *)
type 'a observer = (proof_status * 'a) option -> (proof_status * 'a) -> unit

  (** needed to detach previously attached observers *)
type observer_id

  (** tactic application failed. @see apply_tactic *)
exception Tactic_failure of exn

  (** one or more observers failed. @see apply_tactic *)
exception Observer_failures of (observer_id * exn) list

  (** failure while updating internal data (: 'a). @see apply_tactic *)
exception Data_failure of exn

(** {2 OO interface} *)

class ['a] status:
  ?history_size:int ->  (** default 20 *)
  ?uri:UriManager.uri ->
  typ:Cic.term -> body:Cic.term Lazy.t -> metasenv:Cic.metasenv ->
  attrs:Cic.attribute list ->
  (proof_status -> 'a) -> (* init data *)
  (proof_status * 'a -> proof_status -> 'a) ->  (* update data *)
  unit ->
  object

    method proof: ProofEngineTypes.proof
    method metasenv: Cic.metasenv
    method body: Cic.term Lazy.t
    method typ: Cic.term
    method attrs: Cic.attribute list

    (** change metasenv _without_ triggering any notification *)
    method set_metasenv: Cic.metasenv -> unit

    (** goal -> conjecture
    * @raise CicUtil.Meta_not_found *)
    method conjecture: int -> Cic.conjecture

    method proof_completed: bool
    method goal: int              (** @raise No_goal_left *)
    method set_goal: int -> unit  (** @raise Data_failure *)

    method uri: UriManager.uri option
    method set_uri: UriManager.uri -> unit  (** @raise Uri_redefinition *)

    (** @raise Tactic_failure
    * @raise Observer_failures
    * @raise Data_failure
    *
    * In case of tactic failure, internal status is left unchanged.
    * In case of observer failures internal status will be changed and is
    * granted that all observer will be invoked collecting their failures.
    * In case of data failure, internal status is left unchanged (rolling back
    * last tactic application if needed)
    *)
    method apply_tactic: ProofEngineTypes.tactic -> unit

    method undo: ?steps:int -> unit -> unit
    method redo: ?steps:int -> unit -> unit

    method attach_observer:
      ?interested_in:(event list) -> 'a observer -> observer_id

    method detach_observer: observer_id -> unit

    (** force a notification to all observer, old status is passed as None *)
    method notify: unit

  end

val trivial_status:
  ?uri:UriManager.uri ->
  typ:Cic.term -> body:Cic.term Lazy.t -> metasenv:Cic.metasenv ->
  attrs:Cic.attribute list ->
  unit ->
    unit status

