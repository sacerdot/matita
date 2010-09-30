(* Copyright (C) 2004-2005, HELM Team.
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

exception Option_error of string * string
exception Statement_error of string
exception Command_error of string

let command_error msg = raise (Command_error msg)

type incomplete_proof = {
  proof: ProofEngineTypes.proof;
  stack: Continuationals.Stack.t;
}

type proof_status =
  | No_proof
  | Incomplete_proof of incomplete_proof
  | Proof of ProofEngineTypes.proof
  | Intermediate of Cic.metasenv
      (* Status in which the proof could be while it is being processed by the
      * engine. No status entering/exiting the engine could be in it. *)

class status = fun (b : string) ->
 let fake_obj =
  NUri.uri_of_string "cic:/matita/dummy.decl",0,[],[],
   NCic.Constant([],"",None,NCic.Implicit `Closed,(`Provided,`Theorem,`Regular))
 in
  object
   val moo_content_rev = ([] : GrafiteMarshal.moo)
   val proof_status = No_proof
   val objects = ([] : UriManager.uri list)
   val coercions = CoercDb.empty_coerc_db
   val automation_cache = AutomationCache.empty ()
   val baseuri = b
   val ng_mode = (`CommandMode : [`CommandMode | `ProofMode])
   method moo_content_rev = moo_content_rev
   method set_moo_content_rev v = {< moo_content_rev = v >}
   method proof_status = proof_status
   method set_proof_status v = {< proof_status = v >}
   method objects = objects
   method set_objects v = {< objects = v >}
   method coercions = coercions
   method set_coercions v = {< coercions = v >}
   method automation_cache = automation_cache
   method set_automation_cache v = {< automation_cache = v >}
   method baseuri = baseuri
   method set_baseuri v = {< baseuri = v >}
   method ng_mode = ng_mode;
   method set_ng_mode v = {< ng_mode = v >}
   (* Warning: #stack and #obj are meaningful iff #ng_mode is `ProofMode *)
   inherit ([Continuationals.Stack.t] NTacStatus.status fake_obj (Continuationals.Stack.empty))
 end

let get_current_proof status =
  match status#proof_status with
  | Incomplete_proof { proof = p } -> p
  | Proof p -> p
  | _ -> raise (Statement_error "no ongoing proof")

let get_proof_metasenv status =
  match status#proof_status with
  | No_proof -> []
  | Proof (_, metasenv, _, _, _, _)
  | Incomplete_proof { proof = (_, metasenv, _, _, _, _) }
  | Intermediate metasenv ->
      metasenv

let get_stack status =
  match status#proof_status with
  | Incomplete_proof p -> p.stack
  | Proof _ -> Continuationals.Stack.empty
  | _ -> assert false

let set_stack stack status =
  match status#proof_status with
  | Incomplete_proof p ->
      status#set_proof_status (Incomplete_proof { p with stack = stack })
  | Proof _ ->
      assert (Continuationals.Stack.is_empty stack);
      status
  | _ -> assert false

let set_metasenv metasenv status =
  let proof_status =
    match status#proof_status with
    | No_proof -> Intermediate metasenv
    | Incomplete_proof ({ proof = (uri, _, subst, proof, ty, attrs) } as incomplete_proof) ->
        Incomplete_proof
          { incomplete_proof with proof = (uri, metasenv, subst, proof, ty, attrs) }
    | Intermediate _ -> Intermediate metasenv 
    | Proof (_, metasenv', _, _, _, _) ->
       assert (metasenv = metasenv');
       status#proof_status
  in
   status#set_proof_status proof_status

let get_proof_context status goal =
  match status#proof_status with
  | Incomplete_proof { proof = (_, metasenv, _, _, _, _) } ->
      let (_, context, _) = CicUtil.lookup_meta goal metasenv in
      context
  | _ -> []

let get_proof_conclusion status goal =
  match status#proof_status with
  | Incomplete_proof { proof = (_, metasenv, _, _, _, _) } ->
      let (_, _, conclusion) = CicUtil.lookup_meta goal metasenv in
      conclusion
  | _ -> raise (Statement_error "no ongoing proof")
 
let add_moo_content cmds status =
  let content = status#moo_content_rev in
  let content' =
    List.fold_right
      (fun cmd acc ->
(*         prerr_endline ("adding to moo command: " ^ GrafiteAstPp.pp_command cmd); *)
        match cmd with
        | GrafiteAst.Default _ 
        | GrafiteAst.Index _
        | GrafiteAst.Coercion _ ->
            if List.mem cmd content then acc
            else cmd :: acc
        | _ -> cmd :: acc)
      cmds content
  in
(*   prerr_endline ("new moo content: " ^ String.concat " " (List.map
    GrafiteAstPp.pp_command content')); *)
   status#set_moo_content_rev content'

let dump_status status = 
  HLog.message "status.aliases:\n";
  HLog.message "status.proof_status:"; 
  HLog.message
    (match status#proof_status with
    | No_proof -> "no proof\n"
    | Incomplete_proof _ -> "incomplete proof\n"
    | Proof _ -> "proof\n"
    | Intermediate _ -> "Intermediate\n");
  HLog.message "status.options\n";
  HLog.message "status.coercions\n";
  HLog.message "status.objects:\n";
  List.iter 
    (fun u -> HLog.message (UriManager.string_of_uri u)) status#objects 
