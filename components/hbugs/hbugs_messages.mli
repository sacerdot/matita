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

open Hbugs_types;;

exception Parse_error of string * string  (* parsing subject, reason *)
exception Unexpected_message of message;;

val msg_of_string: string -> message
val string_of_msg: message -> string

val submit_req: url:string -> message -> message
  (** close outchan afterwards *)
val respond_msg: message -> out_channel -> unit
  (** close outchan afterwards *)
  (* exception_name, exception_value, output_channel *)
val respond_exc: string -> string -> out_channel -> unit

(* TODO the below functions are for debugging only and shouldn't be exposed *)
val parse_state:
  ('a Pxp_document.node Pxp_document.extension as 'a) Pxp_document.node ->
    (string * string * int)
val pp_state: (string * string * int) option -> string

