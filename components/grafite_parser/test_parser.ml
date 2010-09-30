(* Copyright (C) 2005, HELM Team.
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

let _ = Helm_registry.load_from "test_parser.conf.xml"

let xml_stream_of_markup =
  let rec print_box (t: CicNotationPres.boxml_markup) =
    Box.box2xml print_mpres t
  and print_mpres (t: CicNotationPres.mathml_markup) =
    Mpresentation.print_mpres print_box t
  in
  print_mpres

let dump_xml t id_to_uri fname =
  prerr_endline (sprintf "dumping MathML to %s ..." fname);
  flush stdout;
  let oc = open_out fname in
  let markup =
   CicNotationPres.render ~lookup_uri:(CicNotationPres.lookup_uri id_to_uri)t in
  let xml_stream = CicNotationPres.print_xml markup in
  Xml.pp_to_outchan xml_stream oc;
  close_out oc

let extract_loc =
  function
    | GrafiteAst.Executable (loc, _)
    | GrafiteAst.Comment (loc, _) -> loc

let pp_associativity = function
  | Gramext.LeftA -> "left"
  | Gramext.RightA -> "right"
  | Gramext.NonA -> "non"

let pp_precedence = string_of_int

(* let last_rule_id = ref None *)

let process_stream istream =
  let char_count = ref 0 in
  let module P = CicNotationPt in
  let module G = GrafiteAst in
  let status =
   ref
    (CicNotation2.load_notation (new LexiconEngine.status)
      ~include_paths:[] (Helm_registry.get "notation.core_file"))
  in
    try
      while true do
        try
         match
          GrafiteParser.parse_statement ~include_paths:[] istream !status
         with
            newstatus, GrafiteParser.LNone _ -> status := newstatus
          | newstatus, GrafiteParser.LSome statement ->
              status := newstatus;
              let floc = extract_loc statement in
              let (_, y) = HExtlib.loc_of_floc floc in
              char_count := y + !char_count;
              match statement with
    (*           | G.Executable (_, G.Macro (_, G.Check (_,
                P.AttributedTerm (_, P.Ident _)))) -> 
                  prerr_endline "mega hack";
                  (match !last_rule_id with
                  | None -> ()
                  | Some id ->
                      prerr_endline "removing last notation rule ...";
                      CicNotationParser.delete id) *)
              | G.Executable (_, G.Macro (_, G.Check (_, t))) -> 
                  prerr_endline (sprintf "ast: %s" (CicNotationPp.pp_term t));
                  let t' = TermContentPres.pp_ast t in
                  prerr_endline (sprintf "rendered ast: %s"
                    (CicNotationPp.pp_term t'));
                  let tbl = Hashtbl.create 0 in
                  dump_xml t' tbl "out.xml"
              | statement ->
                  prerr_endline
                   ("Unsupported statement: " ^
                     GrafiteAstPp.pp_statement
                      ~map_unicode_to_tex:(Helm_registry.get_bool
                        "matita.paste_unicode_as_tex")
                      ~term_pp:CicNotationPp.pp_term
                      ~lazy_term_pp:(fun _ -> "_lazy_term_here_")
                      ~obj_pp:(fun _ -> "_obj_here_")
                      statement)
        with
        | End_of_file -> raise End_of_file
        | HExtlib.Localized (floc,CicNotationParser.Parse_error msg) ->
            let (x, y) = HExtlib.loc_of_floc floc in
(*             let before = String.sub line 0 x in
            let error = String.sub line x (y - x) in
            let after = String.sub line y (String.length line - y) in
            eprintf "%s[01;31m%s[00m%s\n" before error after;
            prerr_endline (sprintf "at character %d-%d: %s" x y msg) *)
            prerr_endline (sprintf "Parse error at character %d-%d: %s"
              (!char_count + x) (!char_count + y) msg)
        | exn ->
            prerr_endline
              (sprintf "TestParser: Uncaught exception: %s" (Printexc.to_string exn))
	done
    with End_of_file -> ()

let _ =
  let arg_spec = [ ] in
  let usage = "" in
  Arg.parse arg_spec (fun _ -> raise (Arg.Bad usage)) usage;
  print_endline "Loading builtin notation ...";
  print_endline "done.";
  flush stdout;
  process_stream (Ulexing.from_utf8_channel stdin)

