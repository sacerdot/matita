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

(* $Id$ *)

(* open CicReduction
open ProofEngineTypes
open UriManager *)

(** DEBUGGING *)

  (** perform debugging output? *)
let debug = false
let debug_print = fun _ -> ()

  (** debugging print *)
let info s = debug_print (lazy ("TACTICALS INFO: " ^ (Lazy.force s)))

module PET = ProofEngineTypes

let id_tac = 
 let id_tac (proof,goal) = 
  let _, metasenv, _, _, _, _ = proof in
  let _, _, _ = CicUtil.lookup_meta goal metasenv in
  (proof,[goal])
 in 
  PET.mk_tactic id_tac

let fail_tac =
 let fail_tac (proof,goal) =
  let _, metasenv, _, _ , _, _ = proof in
  let _, _, _ = CicUtil.lookup_meta goal metasenv in
   raise (PET.Fail (lazy "fail tactical"))
 in
  PET.mk_tactic fail_tac

type goal = PET.goal

    (** TODO needed until tactics start returning both opened and closed goals
     * First part of the function performs a diff among goals ~before tactic
     * application and ~after it. Second part will add as both opened and closed
     * the goals which are returned as opened by the tactic *)
let goals_diff ~before ~after ~opened =
  let sort_opened opened add =
    opened @ (List.filter (fun g -> not (List.mem g opened)) add)
  in
  let remove =
    List.fold_left
      (fun remove e -> if List.mem e after then remove else e :: remove)
      [] before
  in
  let add =
    List.fold_left
      (fun add e -> if List.mem e before then add else e :: add)
      []
      after
  in
  let add, remove = (* adds goals which have been both opened _and_ closed *)
    List.fold_left
      (fun (add, remove) opened_goal ->
        if List.mem opened_goal before
        then opened_goal :: add, opened_goal :: remove
        else add, remove)
      (add, remove)
      opened
  in
  sort_opened opened add, remove

module ProofEngineStatus =
struct
  module Stack = Continuationals.Stack

  (* The stack is used and saved only at the very end of the eval function;
     it is read only at the beginning of the eval;
     we need it just to apply several times in a row this machine to an
     initial stack, i.e. to chain several applications of the machine together,
     i.e. to dump and restore the state of the machine.
     The stack is never used by the tactics: each tactic of type
     PET.tactic ignore the stack. To make a tactic from the eval function
     of a machine we apply the eval on a fresh stack (via the mk_tactic). *)
  type input_status =
    PET.status (* (proof, goal) *) * Stack.t

  type output_status =
    (PET.proof * goal list * goal list) * Stack.t

  type tactic = PET.tactic

  (* f is an eval function of a machine;
     the machine is applied to a fresh stack and the final stack is read
     back to obtain the result of the tactic *)
  let mk_tactic f =
    PET.mk_tactic
      (fun ((proof, goal) as pstatus) ->
        let stack = [ [ 1, Stack.Open goal ], [], [], `NoTag ] in
        let istatus = pstatus, stack in
        let (proof, _, _), stack = f istatus in
        let opened = Continuationals.Stack.open_goals stack in
        proof, opened)

  (* it applies a tactic ignoring (and preserving) the stack *)
  let apply_tactic tac ((proof, _) as pstatus, stack) =
    let proof', opened = PET.apply_tactic tac pstatus in
    let before = PET.goals_of_proof proof in
    let after = PET.goals_of_proof proof' in
    let opened_goals, closed_goals = goals_diff ~before ~after ~opened in
    (proof', opened_goals, closed_goals), stack

  let goals ((_, opened, closed), _) = opened, closed

  (* Done only at the beginning of the eval of the machine *)
  let get_stack = snd
  (* Done only at the end of the eval of the machine *)
  let set_stack stack (opstatus, _) = opstatus, stack

  let inject ((proof, _), stack) = ((proof, [], []), stack)
  let focus goal ((proof, _, _), stack) = (proof, goal), stack
end

module S = ProofEngineStatus
module C = Continuationals.Make (S)

type tactic = S.tactic

let fold_eval status ts =
  let istatus =
    List.fold_left (fun istatus t -> S.focus ~-1 (C.eval t istatus)) status ts
  in
  S.inject istatus

(* Tacticals implemented on top of tynycals *)

let thens ~start ~continuations =
  S.mk_tactic
    (fun istatus ->
      fold_eval istatus
        ([ C.Tactical (C.Tactic start); C.Branch ]
        @ (HExtlib.list_concat ~sep:[ C.Shift ]
            (List.map (fun t -> [ C.Tactical (C.Tactic t) ]) continuations))
        @ [ C.Merge ]))

let then_ ~start ~continuation =
  S.mk_tactic
    (fun istatus ->
      let ostatus = C.eval (C.Tactical (C.Tactic start)) istatus in
      let opened,closed = S.goals ostatus in
       match opened with
          [] -> ostatus
        | _ ->
          fold_eval (S.focus ~-1 ostatus)
            [ C.Semicolon;
              C.Tactical (C.Tactic continuation) ])

let seq ~tactics =
  S.mk_tactic
    (fun istatus ->
      fold_eval istatus
        (HExtlib.list_concat ~sep:[ C.Semicolon ]
          (List.map (fun t -> [ C.Tactical (C.Tactic t) ]) tactics)))

(* Tacticals that cannot be implemented on top of tynycals *)

let const_tac res = PET.mk_tactic (fun _ -> res)

let if_ ~start ~continuation ~fail =
   let if_ status =
      let xoutput = 
         try
	    let result = PET.apply_tactic start status in
	    info (lazy ("Tacticals.if_: succedeed!!!"));
	    Some result 
	 with PET.Fail _ -> None
      in
      let tactic = match xoutput with
         | Some res -> then_ ~start:(const_tac res) ~continuation
	 | None     -> fail
      in 
      PET.apply_tactic tactic status
   in
   PET.mk_tactic if_

let ifs ~start ~continuations ~fail =
   let ifs status =
      let xoutput = 
         try
	    let result = PET.apply_tactic start status in
	    info (lazy ("Tacticals.ifs: succedeed!!!"));
	    Some result 
	 with PET.Fail _ -> None
      in
      let tactic = match xoutput with
         | Some res -> thens ~start:(const_tac res) ~continuations
	 | None     -> fail
      in 
      PET.apply_tactic tactic status
   in
   PET.mk_tactic ifs

let first ~tactics =
  let rec first ~(tactics: tactic list) status =
    info (lazy "in Tacticals.first");
    match tactics with
      [] -> raise (PET.Fail (lazy "first: no tactics left"))
    | tac::tactics ->
        try
         let res = PET.apply_tactic tac status in
          info (lazy ("Tacticals.first: succedeed!!!"));
          res
        with 
         PET.Fail _ -> first ~tactics status
  in
  PET.mk_tactic (first ~tactics)

let rec do_tactic ~n ~tactic =
 PET.mk_tactic
  (function status ->
    if n = 0 then
     PET.apply_tactic id_tac status
    else
     PET.apply_tactic
      (then_ ~start:tactic ~continuation:(do_tactic ~n:(n-1) ~tactic))
      status)

(* This applies tactic and catches its possible failure *)
let try_tactic ~tactic =
 let try_tactic status =
  try
    PET.apply_tactic tactic status
  with (PET.Fail _) as e -> 
    info (lazy (
      "Tacticals.try_tactic failed with exn: " ^ Printexc.to_string e));
    PET.apply_tactic id_tac status
 in
  PET.mk_tactic try_tactic

let rec repeat_tactic ~tactic =
 ProofEngineTypes.mk_tactic
  (fun status ->
    ProofEngineTypes.apply_tactic
     (then_ ~start:tactic
       ~continuation:(try_tactic (repeat_tactic ~tactic))) status)

(* This tries tactics until one of them solves the goal *)
let solve_tactics ~tactics =
 let rec solve_tactics ~(tactics: tactic list) status =
  info (lazy "in Tacticals.solve_tactics");
  match tactics with
  | currenttactic::moretactics ->
      (try
        let (proof, opened) as output_status =
         PET.apply_tactic currenttactic status 
        in
        match opened with 
          | [] -> info (lazy ("Tacticals.solve_tactics: solved the goal!!!"));
                  output_status
          | _ -> info (lazy ("Tacticals.solve_tactics: try the next tactic"));
                 raise (PET.Fail (lazy "Goal not solved"))
       with (PET.Fail _) as e ->
         info (lazy (
            "Tacticals.solve_tactics: current tactic failed with exn: "
            ^ Printexc.to_string e));
         solve_tactics ~tactics:moretactics status)
  | [] ->
      raise (PET.Fail
        (lazy "solve_tactics cannot solve the goal"))
 in
  PET.mk_tactic (solve_tactics ~tactics)

let progress_tactic ~tactic =
  let msg = lazy "Failed to progress" in
  let progress_tactic (((_,metasenv,_,_,_,_),g) as istatus) =
    let ((_,metasenv',_,_,_,_),opened) as ostatus =
     PET.apply_tactic tactic istatus
    in
    match opened with
    | [g1] ->
        let _,oc,oldty = CicUtil.lookup_meta g metasenv in
        let _,nc,newty = CicUtil.lookup_meta g1 metasenv' in
        if oldty = newty && oc = nc then
          raise (PET.Fail msg)
        else
          ostatus
    | _ -> ostatus
  in
  PET.mk_tactic progress_tactic
