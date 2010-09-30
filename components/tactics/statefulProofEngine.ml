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

(* $Id$ *)

let default_history_size = 20

exception No_goal_left
exception Uri_redefinition
type event = [ `Proof_changed | `Proof_completed ]
let all_events = [ `Proof_changed; `Proof_completed ]
let default_events: event list = [ `Proof_changed ]

type proof_status = ProofEngineTypes.proof * ProofEngineTypes.goal option

type 'a observer = (proof_status * 'a) option -> (proof_status * 'a) -> unit
type observer_id = int

exception Observer_failures of (observer_id * exn) list
exception Tactic_failure of exn
exception Data_failure of exn

class ['a] status
  ?(history_size = default_history_size)
  ?uri ~typ ~body ~metasenv ~attrs init_data compute_data ()
  =
  let next_observer_id =
    let next_id = ref 0 in
    fun () ->
      incr next_id;
      !next_id
  in
  let _subst = ([] : Cic.substitution) in
  let initial_proof = ((uri: UriManager.uri option), metasenv, _subst, body, typ, attrs) in
  let next_goal (goals, proof) =
    match goals, proof with
    | goal :: _, _ -> Some goal
    | [], (_, (goal, _, _) :: _, _, _, _, _) ->
        (* the tactic left no open goal: let's choose the first open goal *)
        Some goal
    | _, _ -> None
  in
  let initial_goal = next_goal ([], initial_proof) in
  object (self)

    val mutable _proof = initial_proof
    val mutable _goal = initial_goal
    val mutable _data: 'a = init_data (initial_proof, initial_goal)

      (* event -> (id, observer) list *)
    val observers = Hashtbl.create 7

      (* assumption: all items in history are uncompleted proofs, thus option on
      * goal could be ignored and goal are stored as bare integers *)
    val history = new History.history history_size

    initializer
      history#push self#internal_status

    method proof = _proof
    method private status = (_proof, _goal)  (* logic status *)
    method private set_status (proof, (goal: int option)) =
      _proof <- proof;
      _goal <- goal

    method goal =
      match _goal with
      | Some goal -> goal
      | None -> raise No_goal_left

      (* what will be kept in history *)
    method private internal_status = (self#status, _data)
    method private set_internal_status (status, data) =
      self#set_status status;
      _data <- data

    method set_goal goal =
      _goal <- Some goal
(*
      let old_internal_status = self#internal_status in
      _goal <- Some goal;
      try
        self#update_data old_internal_status;
        history#push self#internal_status;
        self#private_notify (Some old_internal_status)
      with (Data_failure _) as exn ->
        self#set_internal_status old_internal_status;
        raise exn
*)

    method uri      = let (uri, _, _, _, _, _)      = _proof in uri
    method metasenv = let (_, metasenv, _, _, _, _) = _proof in metasenv
    method body     = let (_, _, _, body, _, _)     = _proof in body
    method typ      = let (_, _, _, _, typ, _)      = _proof in typ
    method attrs    = let (_, _, _, _, _, attrs)    = _proof in attrs

    method set_metasenv metasenv =
      let (uri, _,  _subst,body, typ, attes) = _proof in
      _proof <- (uri, metasenv,  _subst,body, typ, attrs)

    method set_uri uri =
      let (old_uri, metasenv,  _subst,body, typ, attrs) = _proof in
      if old_uri <> None then
        raise Uri_redefinition;
      _proof <- (Some uri, metasenv,  _subst,body, typ, attrs)

    method conjecture goal =
      let (_, metasenv, _subst, _, _, _) = _proof in
      CicUtil.lookup_meta goal metasenv

    method apply_tactic tactic =
      let old_internal_status = self#internal_status in
      let (new_proof, new_goals) =
        try
          ProofEngineTypes.apply_tactic tactic (_proof, self#goal)
        with exn -> raise (Tactic_failure exn)
      in
      _proof <- new_proof;
      _goal <- next_goal (new_goals, new_proof);
      try
        self#update_data old_internal_status;
        history#push self#internal_status;
        self#private_notify (Some old_internal_status)
      with (Data_failure _) as exn ->
        self#set_internal_status old_internal_status;
        raise exn

    method proof_completed = _goal = None

    method attach_observer ?(interested_in = default_events) observer
      =
      let id = next_observer_id () in
      List.iter
        (fun event ->
          let prev_observers =
            try Hashtbl.find observers event with Not_found -> []
          in
          Hashtbl.replace observers event ((id, observer)::prev_observers))
        interested_in;
      id

    method detach_observer id =
      List.iter
        (fun event ->
          let prev_observers =
            try Hashtbl.find observers event with Not_found -> []
          in
          let new_observers =
            List.filter (fun (id', _) -> id' <> id) prev_observers
          in
          Hashtbl.replace observers event new_observers)
        all_events

    method private private_notify old_internal_status =
      let cur_internal_status = (self#status, _data) in
      let exns = ref [] in
      let notify (id, observer) =
        try
          observer old_internal_status cur_internal_status
        with exn -> exns := (id, exn) :: !exns
      in
      List.iter notify
        (try Hashtbl.find observers `Proof_changed with Not_found -> []);
      if self#proof_completed then
        List.iter notify
          (try Hashtbl.find observers `Proof_completed with Not_found -> []);
      match !exns with
      | [] -> ()
      | exns -> raise (Observer_failures exns)

    method private update_data old_internal_status =
      (* invariant: _goal and/or _proof has been changed
       * invariant: proof is not yet completed *)
      let status = self#status in
      try
        _data <- compute_data old_internal_status status
      with exn -> raise (Data_failure exn)

    method undo ?(steps = 1) () =
      let ((proof, goal), data) = history#undo steps in
      _proof <- proof;
      _goal <- goal;
      _data <- data;
      self#private_notify None

    method redo ?(steps = 1) () = self#undo ~steps:~-steps ()

    method notify = self#private_notify None

  end

let trivial_status ?uri ~typ ~body ~metasenv ~attrs () =
  new status ?uri ~typ ~body ~metasenv ~attrs (fun _ -> ()) (fun _ _ -> ()) ()

