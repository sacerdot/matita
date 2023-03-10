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

open Printf

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

  (* source files for tables xml parsing (if unmarshall=false) *)
let xml_tables = [
(*
  `Entities, "/usr/share/gtkmathview/entities-table.xml";
  `Dictionary, "/usr/share/editex/dictionary-tex.xml"
*)
  `Entities, "data/entities-table.xml";
  `Dictionary, "data/dictionary-tex.xml";
  `Entities, "data/extra-entities.xml";
  (** extra-entities.xml should be the last one since it is used to override
   * previous mappings. Add there overrides as needed. *)
]

let iter_gen record_tag name_field value_field f fname =
  let start_element tag attrs =
    if tag = record_tag then
      try
        let name = List.assoc name_field attrs in
        let value = List.assoc value_field attrs in
        f name value
      with Not_found -> ()
  in
  let callbacks = {
    XmlPushParser.default_callbacks with
      XmlPushParser.start_element = Some start_element
  } in
  let xml_parser = XmlPushParser.create_parser callbacks in
  XmlPushParser.parse xml_parser (`File fname)

let iter_entities_file    = iter_gen "entity" "name" "value"
let iter_dictionary_file  = iter_gen "entry" "name" "val"

let parse_from_xml () =
  let macro2utf8 = Hashtbl.create 2000 in
  let add_macro macro utf8 =
    debug_print (lazy (sprintf "Adding macro %s = '%s'" macro utf8));
    Hashtbl.replace macro2utf8 macro utf8
  in
  let fill_table () =
    List.iter
      (fun (typ, fname) ->
        match typ with
        | `Entities -> iter_entities_file add_macro fname
        | `Dictionary -> iter_dictionary_file add_macro fname)
      xml_tables
  in
  fill_table ();
  macro2utf8

let main () =
  let oc = open_out Sys.argv.(1) in
  let oc_doc = open_out Sys.argv.(2) in
  output_string oc "(* GENERATED by make_table: DO NOT EDIT! *)\n";
  output_string oc_doc "(* GENERATED by make_table: DO NOT EDIT! *)\n";
  output_string oc "let macro2utf8 = Hashtbl.create 2000\n";
  output_string oc "let utf82macro = Hashtbl.create 2000\n";
  output_string oc "let data = [\n";
  let macro2utf8 = parse_from_xml () in
  Hashtbl.iter
    (fun macro utf8 ->
            fprintf oc "  \"%s\", \"%s\";\n" macro (String.escaped utf8);
            fprintf oc_doc "\\%s %s\n" macro utf8)
    macro2utf8;
  output_string oc "  ];;\n";
  output_string oc "let _ =\n";
  output_string oc "  List.iter\n";
  output_string oc "    (fun (macro, utf8) ->\n";
  output_string oc "      Hashtbl.replace macro2utf8 macro utf8;\n";
  output_string oc "      Hashtbl.replace utf82macro utf8 macro)\n";
  output_string oc "    data;;\n";
  close_out oc;
  close_out oc_doc

let _ = main ()

