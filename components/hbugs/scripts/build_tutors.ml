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
#use "topfind"
#require "pcre"
#require "pxp"
open Printf
open Pxp_document
open Pxp_dtd
open Pxp_types
open Pxp_yacc

let index = "data/tutors_index.xml"
let template = "data/hbugs_tutor.TPL.ml"

  (* apply a set of regexp substitutions specified as a list of pairs
  <pattern,template> to a string *)
let rec apply_subst ~fill s =
  match fill with
  | [] -> s
  | (pat, templ)::rest ->
      apply_subst ~fill:rest (Pcre.replace ~pat ~templ s)
  (* fill a ~template file with substitutions specified in ~fill (see
  apply_subst) and save output to ~output *)
let fill_template ~template ~fill ~output =
  printf "Creating %s ... " output; flush stdout;
  let (ic, oc) = (open_in template, open_out output) in
  let rec fill_template' () =
    output_string oc ((apply_subst ~fill (input_line ic)) ^ "\n");
    fill_template' ()
  in
  try
    output_string oc (sprintf
"(*
  THIS CODE IS GENERATED - DO NOT MODIFY!

  the source of this code is template \"%s\"
  the template was filled with data read from \"%s\"
*)\n"
      template index);
    fill_template' ()
  with End_of_file ->
    close_in ic;
    close_out oc;
    printf "done!\n"; flush stdout
let parse_xml fname =
  parse_wfdocument_entity default_config (from_file fname) default_spec
let is_tutor node =
  match node#node_type with T_element "tutor" -> true | _ -> false
let is_element node =
  match node#node_type with T_element _ -> true | _ -> false
let main () =
  (parse_xml index)#root#iter_nodes
    (fun node ->
      try
        (match node with
        | node when is_tutor node ->
            (try  (* skip hand-written tutors *)
              ignore (find_element "no_auto" node);
              raise Exit
            with Not_found -> ());
            let output =
              try
                (match node#attribute "source" with
                | Value s -> s
                | _ -> assert false)
              with Not_found -> assert false
            in
            let fill =
              List.map  (* create substitution list from index data *)
                (fun node ->
                  let name =  (* node name *)
                    (match node#node_type with
                    | T_element s -> s
                    | _ -> assert false)
                  in
                  let value = node#data in  (* node value *)
                  (sprintf "@%s@" (String.uppercase name),  (* pattern *)
                   value))                                  (* substitution *)
                (List.filter is_element node#sub_nodes)
            in
            fill_template ~fill ~template ~output
        | _ -> ())
      with Exit -> ())

let _ = main ()

