#!/usr/bin/ocamlrun /usr/bin/ocaml
(* Copyright (C) 2006, HELM Team.
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

let fname =
  try Sys.argv.(1)
  with Invalid_argument _ ->
    prerr_endline "Usage: split.ml <FILE.html>";
    exit 1 ;;

#use "topfind";;
#require "unix";;
#require "pxp-engine";;
#require "pxp-lex-utf8";;

open Printf

let xhtml_header title =
  sprintf
"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
  <head>
    <title>%s</title>
  </head>
  <body>
"
  title

let xhtml_trailer =
"  </body>
</html>
"

type 'a node =
  ('a Pxp_document.node #Pxp_document.extension as 'a) Pxp_document.node

let resolver =
  Pxp_reader.lookup_public_id_as_file [
    "-//W3C//DTD XHTML 1.0 Transitional//EN", "xhtml1-transitional.dtd";
    "-//W3C//ENTITIES Latin 1 for XHTML//EN", "xhtml-lat1.ent";
    "-//W3C//ENTITIES Symbols for XHTML//EN", "xhtml-symbol.ent";
    "-//W3C//ENTITIES Special for XHTML//EN", "xhtml-special.ent"; ]

let parse_xml fname =
  Pxp_tree_parser.parse_wfdocument_entity
    { Pxp_types.default_config with Pxp_types.encoding = `Enc_utf8 }
    (Pxp_types.from_file ~alt:[ resolver ] fname)
    Pxp_tree_parser.default_spec

  (** pattern matching like predicate on pxp nodes *)
let match_elt tag attr_name ?attr_value () node =
  node#node_type = Pxp_document.T_element tag
  && (match attr_value with
     | Some attr_value ->
         (try node#attribute attr_name = Pxp_types.Value attr_value
          with Not_found -> false)
     | None -> List.mem attr_name node#attribute_names)

let slice doc =
  let article =
    try
      Pxp_document.find ~deeply:true
        (match_elt "div" "class" ~attr_value:"article" ()) doc#root
     with Not_found -> failwith "Can't find article <div>" in
  let titlepage =
    Pxp_document.find ~deeply:false
      (match_elt "div" "class" ~attr_value:"titlepage" ()) article in
  let toc =
    Pxp_document.find ~deeply:false
      (match_elt "div" "class" ~attr_value:"toc" ()) article in
  let secs =
    Pxp_document.find_all ~deeply:false
      (match_elt "div" "class" ~attr_value:"sect1" ()) article in
  let title =
    Pxp_document.find ~deeply:true
      (fun node -> node#node_type = Pxp_document.T_element "title") doc#root in
  title#data,
  titlepage :: toc :: secs

let localize_ids secs =
  let id2sec = Hashtbl.create 1023 in
  let sec_ids = ref [] in
  List.iter
    (fun sec ->
      match Pxp_document.find_all ~deeply:true (match_elt "a" "id" ()) sec with
      | sec_id :: ids ->
          let sec_id = sec_id#required_string_attribute "id" in
          sec_ids := sec_id :: !sec_ids;
          List.iter
            (fun id ->
              let id = id#required_string_attribute "id" in
              Hashtbl.add id2sec id sec_id)
            ids
      | _ -> failwith "can't find section id")
    secs;
  !sec_ids, id2sec

let fname_of_sec sec_name = sec_name ^ ".html"

let get_sec_id sec =
  let id =
    try
      Pxp_document.find ~deeply:true (match_elt "a" "id" ()) sec
    with Not_found -> failwith "can't find section id" in
  id#required_string_attribute "id"

let get_sec_title sec =
  let h2 =
    Pxp_document.find ~deeply:true
      (match_elt "h2" "class" ~attr_value:"title" ()) sec in
  let text =
    List.find (fun node -> node#node_type = Pxp_document.T_data) h2#sub_nodes in
  text#data

let iter_xrefs f node =
  let a_s = Pxp_document.find_all ~deeply:true (match_elt "a" "href" ()) node in
  List.iter
    (fun (node: 'a node) ->
      let href = node#required_string_attribute "href" in
      assert (String.length href > 0);
      if href.[0] = '#' then
        let xref = String.sub href 1 (String.length href - 1) in
        f node xref)
    a_s

let patch_toc sec_ids id2sec toc =
  iter_xrefs
    (fun node xref ->
      if List.mem xref sec_ids then
        node#set_attribute "href" (Pxp_types.Value (fname_of_sec xref))
      else
        try
          let sec = Hashtbl.find id2sec xref in
          node#set_attribute "href"
            (Pxp_types.Value (fname_of_sec sec ^ "#" ^ xref))
        with Not_found -> ())
    toc

let patch_sec sec_ids id2sec sec =
  let sec_name = get_sec_id sec in
  iter_xrefs
    (fun node xref ->
      try
        let xref_sec = Hashtbl.find id2sec xref in
        if xref_sec <> sec_name then
          node#set_attribute "href"
            (Pxp_types.Value (fname_of_sec xref_sec ^ "#" ^ xref))
      with Not_found -> ())
    sec

let open_formatter fname =
  Unix.open_process_out (sprintf "xmllint --format -o %s -" fname)

let close_formatter oc = ignore (Unix.close_process_out oc)

let output_index title (titlepage: 'a node) (toc: 'a node) fname =
  let oc = open_formatter fname in
  output_string oc (xhtml_header title);
  titlepage#write (`Out_channel oc) `Enc_utf8;
  toc#write (`Out_channel oc) `Enc_utf8;
  output_string oc xhtml_trailer;
  close_formatter oc

let output_sec title (sec: 'a node) fname =
  let oc = open_formatter fname in
  output_string oc (xhtml_header (sprintf "%s - %s" title (get_sec_title sec)));
  sec#write (`Out_channel oc) `Enc_utf8;
  output_string oc xhtml_trailer;
  close_formatter oc

let main () =
  let doc = parse_xml fname in
  match slice doc with
  | title, (titlepage :: toc :: secs) ->
      let sec_ids, id2sec = localize_ids secs in
      patch_toc sec_ids id2sec toc;
      List.iter (patch_sec sec_ids id2sec) secs;
      output_index title titlepage toc "index.html";
      List.iter
        (fun sec -> output_sec title sec (get_sec_id sec ^ ".html"))
        secs
  | _ -> failwith "Unrecognized document structure"

let _ = main ()

