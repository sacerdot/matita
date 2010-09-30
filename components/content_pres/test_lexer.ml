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

let _ =
  let level = ref "2@" in
  let ic = ref stdin in
  let arg_spec = [ "-level", Arg.Set_string level, "set the notation level" ] in
  let usage = "test_lexer [ -level level ] [ file ]" in
  let open_file fname =
    if !ic <> stdin then close_in !ic;
    ic := open_in fname
  in
  Arg.parse arg_spec open_file usage;
  let lexer =
    match !level with
	"1" -> CicNotationLexer.level1_pattern_lexer ()
      | "2@" -> CicNotationLexer.level2_ast_lexer ()
      | "2$" -> CicNotationLexer.level2_meta_lexer ()
      | l ->
	  prerr_endline (Printf.sprintf "Unsupported level %s" l);
	  exit 2
  in
  let token_stream, loc_func =
    lexer.Token.tok_func (Obj.magic (Ulexing.from_utf8_channel !ic)) in
  Printf.printf "Lexing notation level %s\n" !level; flush stdout;
  let tok_count = ref 0 in
  let rec dump () =
    let (a,b) = Stream.next token_stream in
    if a = "EOI" then raise Stream.Failure;
    let pos = loc_func !tok_count in
    print_endline (Printf.sprintf "%s '%s' (@ %d-%d)" a b
      (Stdpp.first_pos pos) (Stdpp.last_pos pos));
    incr tok_count;
    dump ()
  in
  try
    dump ()
  with Stream.Failure -> ()

