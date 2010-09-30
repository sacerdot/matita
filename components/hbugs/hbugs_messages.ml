(*
 * Copyright (C) 2003:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open Hbugs_types;;
open Printf;;
open Pxp_document;;
open Pxp_dtd;;
open Pxp_types;;
open Pxp_yacc;;

let debug = 2;; (*  0 -> no debug
                    1 -> waiting for an answer / answer received
                    2 -> XML messages dumping
                *)

exception Attribute_not_found of string;;
exception Empty_node;;  (** found a node with no _element_ children *)
exception No_element_found of string;;
exception Parse_error of string * string;;  (* parsing subject, reason *)
exception Unexpected_message of message;;

let is_xml_element n = match n#node_type with T_element _ -> true | _ -> false
let get_attr node name =
  try
    (match node#attribute name with
    | Value s -> s
    | _ -> raise Not_found)
  with Not_found -> raise (Attribute_not_found name)
let assert_element n name =
  match n#node_type with
  | T_element n when n = name ->
      ()
  | _ -> raise (Parse_error ("", "Expected node: " ^ name))

  (** given a string representation of a proof asistant state (e.g. the first
  child of the XML root of a State_change or Start_musing message), build from
  it an HBugs view of a proof assistant state *)
let parse_state (root: ('a node extension as 'a) node) =
  if (List.filter is_xml_element root#sub_nodes) = [] then
    raise Empty_node;
  let buf = Buffer.create 10240 in
  let node_to_string (node: ('a node extension as 'a) node) =
    Buffer.clear buf;
    node#write (`Out_buffer buf) `Enc_utf8;
    let res = Buffer.contents buf in
    Buffer.clear buf;
    res
  in
  let (goal_node, type_node, body_node) =
    try
      (find_element "CurrentGoal" root,
       find_element "ConstantType" root,
       find_element "CurrentProof" root)
    with Not_found ->
      raise (Parse_error ("", "Malformed HBugs status XML document"))
  in
  assert_element root "gTopLevelStatus";
  assert_element goal_node "CurrentGoal";
  assert_element type_node "ConstantType";
  assert_element body_node "CurrentProof";
  goal_node#write (`Out_buffer buf) `Enc_utf8;
  let (type_string, body_string) =
    (node_to_string type_node, node_to_string body_node)
  in
  let goal =
    try
      int_of_string (goal_node#data)
    with Failure "int_of_string" ->
      raise (Parse_error (goal_node#data, "can't parse goal"))
  in
  (type_string, body_string, goal)

  (** parse an hint from an XML node, XML node should have type 'T_element _'
  (the name is ignored), attributes on it are ignored *)
let parse_hint node =
 let rec parse_hint_node node =
   match node#node_type with
   | T_element "ring" -> Use_ring
   | T_element "fourier" -> Use_fourier
   | T_element "reflexivity" -> Use_reflexivity
   | T_element "symmetry" -> Use_symmetry
   | T_element "assumption" -> Use_assumption
   | T_element "contradiction" -> Use_contradiction
   | T_element "exists" -> Use_exists
   | T_element "split" -> Use_split
   | T_element "left" -> Use_left
   | T_element "right" -> Use_right
   | T_element "apply" -> Use_apply node#data
   | T_element "hints" ->
       Hints
        (List.map parse_hint_node (List.filter is_xml_element node#sub_nodes))
   | _ -> assert false (* CSC: should this assert false be a raise something? *)
 in
  match List.filter is_xml_element node#sub_nodes with
     [node] -> parse_hint_node node
   | _ -> assert false (* CSC: should this assert false be a raise something? *)

let parse_hint_type n = n#data (* TODO parsare il possibile tipo di suggerimento *)
let parse_tutor_dscs n =
  List.map
    (fun n -> (get_attr n "id", n#data))
    (List.filter is_xml_element n#sub_nodes)
let parse_tutor_ids node =
  List.map
    (fun n -> get_attr n "id") (List.filter is_xml_element node#sub_nodes)

let tutors_sep = Pcre.regexp ",\\s*"

let pxp_config = PxpHelmConf.pxp_config
let msg_of_string' s =
  let root =  (* xml tree's root *)
    parse_wfcontent_entity pxp_config (from_string s) PxpHelmConf.pxp_spec
  in
  match root#node_type with

    (* general purpose *)
  | T_element "help" -> Help
  | T_element "usage" -> Usage root#data
  | T_element "exception" -> Exception (get_attr root "name", root#data)

    (* client -> broker *)
  | T_element "register_client" ->
      Register_client (get_attr root "id", get_attr root "url")
  | T_element "unregister_client" -> Unregister_client (get_attr root "id")
  | T_element "list_tutors" -> List_tutors (get_attr root "id")
  | T_element "subscribe" ->
      Subscribe (get_attr root "id", parse_tutor_ids root)
  | T_element "state_change" ->
      let state_node =
        try
          Some (find_element ~deeply:false "gTopLevelStatus" root)
        with Not_found -> None
      in
      State_change
        (get_attr root "id",
        match state_node with
        | Some n -> (try Some (parse_state n) with Empty_node -> None)
        | None -> None)
  | T_element "wow" -> Wow (get_attr root "id")

    (* tutor -> broker *)
  | T_element "register_tutor" ->
      let hint_node = find_element "hint_type" root in
      let dsc_node = find_element "description" root in
      Register_tutor
        (get_attr root "id", get_attr root "url",
        parse_hint_type hint_node, dsc_node#data)
  | T_element "unregister_tutor" -> Unregister_tutor (get_attr root "id")
  | T_element "musing_started" ->
      Musing_started (get_attr root "id", get_attr root "musing_id")
  | T_element "musing_aborted" ->
      Musing_started (get_attr root "id", get_attr root "musing_id")
  | T_element "musing_completed" ->
      let main_node =
        try
          find_element "eureka" root
        with Not_found -> find_element "sorry" root
      in
      Musing_completed
        (get_attr root "id", get_attr root "musing_id",
        (match main_node#node_type with
        | T_element "eureka" ->
            Eureka (parse_hint main_node)
        | T_element "sorry" -> Sorry
        | _ -> assert false)) (* can't be there, see 'find_element' above *)

    (* broker -> client *)
  | T_element "client_registered" -> Client_registered (get_attr root "id")
  | T_element "client_unregistered" -> Client_unregistered (get_attr root "id")
  | T_element "tutor_list" ->
      Tutor_list (get_attr root "id", parse_tutor_dscs root)
  | T_element "subscribed" ->
      Subscribed (get_attr root "id", parse_tutor_ids root)
  | T_element "state_accepted" ->
      State_accepted
        (get_attr root "id",
        List.map
          (fun n -> get_attr n "id")
          (List.filter is_xml_element (find_element "stopped" root)#sub_nodes),
        List.map
          (fun n -> get_attr n "id")
          (List.filter is_xml_element (find_element "started" root)#sub_nodes))
  | T_element "hint" -> Hint (get_attr root "id", parse_hint root)

    (* broker -> tutor *)
  | T_element "tutor_registered" -> Tutor_registered (get_attr root "id")
  | T_element "tutor_unregistered" -> Tutor_unregistered (get_attr root "id")
  | T_element "start_musing" ->
      let state_node =
        try
          find_element ~deeply:false "gTopLevelStatus" root
        with Not_found -> raise (No_element_found "gTopLevelStatus")
      in
      Start_musing (get_attr root "id", parse_state state_node)
  | T_element "abort_musing" ->
      Abort_musing (get_attr root "id", get_attr root "musing_id")
  | T_element "thanks" -> Thanks (get_attr root "id", get_attr root "musing_id")
  | T_element "too_late" ->
      Too_late (get_attr root "id", get_attr root "musing_id")

  | _ -> raise (No_element_found s)

let msg_of_string s =
  try
    msg_of_string' s
  with e -> raise (Parse_error (s, Printexc.to_string e))

let pp_state = function
  | Some (type_string, body_string, goal) ->
    (* ASSUMPTION: type_string and body_string are well formed XML document
    contents (i.e. they don't contain heading <?xml ... ?> declaration nor
    DOCTYPE one *)
    "<gTopLevelStatus>\n" ^
    (sprintf "<CurrentGoal>%d</CurrentGoal>\n" goal) ^
    type_string ^ "\n" ^
    body_string ^ "\n" ^
    "</gTopLevelStatus>\n"
  | None -> "<gTopLevelStatus />\n"

let rec pp_hint = function
  | Use_ring -> sprintf "<ring />"
  | Use_fourier -> sprintf "<fourier />"
  | Use_reflexivity -> sprintf "<reflexivity />"
  | Use_symmetry -> sprintf "<symmetry />"
  | Use_assumption -> sprintf "<assumption />"
  | Use_contradiction -> sprintf "<contradiction />"
  | Use_exists -> sprintf "<exists />"
  | Use_split -> sprintf "<split />"
  | Use_left -> sprintf "<left />"
  | Use_right -> sprintf "<right />"
  | Use_apply term -> sprintf "<apply>%s</apply>" term
  | Hints hints ->
      sprintf "<hints>\n%s\n</hints>"
        (String.concat "\n" (List.map pp_hint hints))

let pp_hint_type s = s   (* TODO pretty print hint_type *)
let pp_tutor_dscs =
  List.fold_left
    (fun s (id, dsc) ->
      sprintf "%s<tutor_dsc id=\"%s\">%s</tutor_dsc>" s id dsc)
    ""
let pp_tutor_ids =
  List.fold_left (fun s id -> sprintf "%s<tutor id=\"%s\" />" s id) ""

let string_of_msg = function
  | Help -> "<help />"
  | Usage usage_string -> sprintf "<usage>%s</usage>" usage_string
  | Exception (name, value) ->
      sprintf "<exception name=\"%s\">%s</exception>" name value
  | Register_client (id, url) ->
      sprintf "<register_client id=\"%s\" url=\"%s\" />" id url
  | Unregister_client id -> sprintf "<unregister_client id=\"%s\" />" id
  | List_tutors id -> sprintf "<list_tutors id=\"%s\" />" id
  | Subscribe (id, tutor_ids) ->
      sprintf "<subscribe id=\"%s\">%s</subscribe>"
        id (pp_tutor_ids tutor_ids)
  | State_change (id, state) ->
      sprintf "<state_change id=\"%s\">%s</state_change>"
        id (pp_state state)
  | Wow id -> sprintf "<wow id=\"%s\" />" id
  | Register_tutor (id, url, hint_type, dsc) ->
      sprintf
"<register_tutor id=\"%s\" url=\"%s\">
<hint_type>%s</hint_type>
<description>%s</description>
</register_tutor>"
        id url (pp_hint_type hint_type) dsc
  | Unregister_tutor id -> sprintf "<unregister_tutor id=\"%s\" />" id
  | Musing_started (id, musing_id) ->
      sprintf "<musing_started id=\"%s\" musing_id=\"%s\" />" id musing_id
  | Musing_aborted (id, musing_id) ->
      sprintf "<musing_aborted id=\"%s\" musing_id=\"%s\" />" id musing_id
  | Musing_completed (id, musing_id, result) ->
      sprintf
        "<musing_completed id=\"%s\" musing_id=\"%s\">%s</musing_completed>"
        id musing_id
        (match result with
        | Sorry -> "<sorry />"
        | Eureka hint -> sprintf "<eureka>%s</eureka>" (pp_hint hint))
  | Client_registered id -> sprintf "<client_registered id=\"%s\" />" id
  | Client_unregistered id -> sprintf "<client_unregistered id=\"%s\" />" id
  | Tutor_list (id, tutor_dscs) ->
      sprintf "<tutor_list id=\"%s\">%s</tutor_list>"
        id (pp_tutor_dscs tutor_dscs)
  | Subscribed (id, tutor_ids) ->
      sprintf "<subscribed id=\"%s\">%s</subscribed>"
        id (pp_tutor_ids tutor_ids)
  | State_accepted (id, stop_ids, start_ids) ->
      sprintf
"<state_accepted id=\"%s\">
<stopped>%s</stopped>
<started>%s</started>
</state_accepted>"
        id
        (String.concat ""
          (List.map (fun id -> sprintf "<musing id=\"%s\" />" id) stop_ids))
        (String.concat ""
          (List.map (fun id -> sprintf "<musing id=\"%s\" />" id) start_ids))
  | Hint (id, hint) -> sprintf "<hint id=\"%s\">%s</hint>" id (pp_hint hint)
  | Tutor_registered id -> sprintf "<tutor_registered id=\"%s\" />" id
  | Tutor_unregistered id -> sprintf "<tutor_unregistered id=\"%s\" />" id
  | Start_musing (id, state) ->
      sprintf "<start_musing id=\"%s\">%s</start_musing>"
        id (pp_state (Some state))
  | Abort_musing (id, musing_id) ->
      sprintf "<abort_musing id=\"%s\" musing_id=\"%s\" />" id musing_id
  | Thanks (id, musing_id) ->
      sprintf "<thanks id=\"%s\" musing_id=\"%s\" />" id musing_id
  | Too_late (id, musing_id) ->
      sprintf "<too_late id=\"%s\" musing_id=\"%s\" />" id musing_id
;;

  (* debugging function that dump on stderr the sent messages *)
let dump_msg msg =
  if debug >= 2 then
    prerr_endline
      (sprintf "<SENDING_MESSAGE>\n%s\n</SENDING_MESSAGE>"
        (match msg with
        | State_change _ -> "<state_change>omissis ...</state_change>"
        | msg -> string_of_msg msg))
;;

let submit_req ~url msg =
  dump_msg msg;
  if debug >= 1 then (prerr_string "Waiting for an answer ... "; flush stderr);
  let res =
    msg_of_string (Hbugs_misc.http_post ~body:(string_of_msg msg) url)
  in
  if debug >= 1 then (prerr_string "answer received!\n"; flush stderr);
  res
;;
let return_xml_msg body outchan =
  Http_daemon.respond ~headers:["Content-Type", "text/xml"] ~body outchan
;;
let respond_msg msg outchan =
  dump_msg msg;
  return_xml_msg (string_of_msg msg) outchan
(*   close_out outchan *)
;;
let respond_exc name value = respond_msg (Exception (name, value));;

