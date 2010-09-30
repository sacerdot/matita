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

open Pxp_document;;
open Pxp_dtd;;
open Pxp_types;;
open Pxp_yacc;;

open Printf;;

let test_data = "HBUGS_MESSAGES.xml" ;;

let test_message (n:('a Pxp_document.extension as 'b) Pxp_document.node as 'a) =
  try
    let msg_string =
      let buf = Buffer.create 1000 in
      n#write (`Out_buffer buf) `Enc_utf8;
      Buffer.contents buf
    in
    let msg = Hbugs_messages.msg_of_string msg_string in
    let pp = Hbugs_messages.string_of_msg msg in
    let msg' = Hbugs_messages.msg_of_string pp in
    if (msg <> msg') then
      prerr_endline
        (sprintf "Failure with msg %s"
          (match n#node_type with T_element name -> name | _ -> assert false))
  with e ->
    prerr_endline
      (sprintf "Failure with msg %s: uncaught exception %s"
        (match n#node_type with T_element name -> name | _ -> assert false)
        (Printexc.to_string e))
;;

let is_xml_element n =
  match n#node_type with T_element _ -> true | _ -> false
;;

let root =
  parse_wfcontent_entity default_config (from_file test_data) default_spec
in
printf "Testing all messages from %s ...\n" test_data; flush stdout;
List.iter test_message (List.filter is_xml_element root#sub_nodes);
printf "Done!\n"
;;

