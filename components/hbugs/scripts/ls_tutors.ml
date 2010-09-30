#!/usr/bin/ocamlrun /usr/bin/ocaml
(*
 * Copyright (C) 2003-2004:
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

(* Usage: ls_tutors.ml        # lists all tutors
 *        ls_tutors.ml -auto  # lists only generated tutors
 *)

#use "topfind"
#require "pxp"
open Printf
open Pxp_document
open Pxp_dtd
open Pxp_types
open Pxp_yacc

let index = "data/tutors_index.xml"
let auto_only =
  try
    (match Sys.argv.(1) with "-auto" -> true | _ -> false)
  with Invalid_argument _ -> false
let parse_xml fname =
  parse_wfdocument_entity default_config (from_file fname) default_spec
let is_tutor node =
  match node#node_type with T_element "tutor" -> true | _ -> false
let main () =
  List.iter
    (fun tutor ->
      try
        (match tutor#attribute "source" with
        | Value s ->
            if not auto_only then
              print_endline s
            else  (* we should print only generated tutors *)
              (try
                ignore (find_element "no_auto" tutor);
              with Not_found ->
                print_endline s)
        | _ -> assert false)
      with Not_found -> assert false)
    (List.filter is_tutor (parse_xml index)#root#sub_nodes)
let _ = main ()

