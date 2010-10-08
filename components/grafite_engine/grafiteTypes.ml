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

class status = fun (b : string) ->
 let fake_obj =
  NUri.uri_of_string "cic:/matita/dummy.decl",0,[],[],
   NCic.Constant([],"",None,NCic.Implicit `Closed,(`Provided,`Theorem,`Regular))
 in
  object
   val moo_content_rev = ([] : GrafiteMarshal.moo)
   val objects = ([] : UriManager.uri list)
   val baseuri = b
   val ng_mode = (`CommandMode : [`CommandMode | `ProofMode])
   method moo_content_rev = moo_content_rev
   method set_moo_content_rev v = {< moo_content_rev = v >}
   method objects = objects
   method set_objects v = {< objects = v >}
   method baseuri = baseuri
   method set_baseuri v = {< baseuri = v >}
   method ng_mode = ng_mode;
   method set_ng_mode v = {< ng_mode = v >}
   (* Warning: #stack and #obj are meaningful iff #ng_mode is `ProofMode *)
   inherit ([Continuationals.Stack.t] NTacStatus.status fake_obj (Continuationals.Stack.empty))
 end

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
  HLog.message "status.options\n";
  HLog.message "status.coercions\n";
  HLog.message "status.objects:\n";
  List.iter 
    (fun u -> HLog.message (UriManager.string_of_uri u)) status#objects 
