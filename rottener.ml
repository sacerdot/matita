(* Copyright (C) 2007, HELM Team.
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

open Printf

module Ast = GrafiteAst
module Pt = CicNotationPt

  (* set to false to change identifier instead of adding extra identifiers *)
let add_ident = ref true

let error_token = "O"
let error_token_len = String.length error_token

let has_toplevel_term = function
  | GrafiteParser.LSome (Ast.Executable (_, Ast.Command (_, Ast.Obj (loc, (
        Pt.Theorem ((`Definition | `Lemma | `Theorem), _, _, _)
      (*| Pt.Inductive _*)
      (*| Pt.Record _*)
    ))))) ->
      true
  | _ -> false

let flush_token_stream (stream, loc_func) =
  let tok_count = ref ~-1 in
  let rec aux acc =
    let next_tok =
      try Some (Stream.next stream) with Stream.Failure -> None in
    match next_tok with
    | None | Some ("EOI", _) -> List.rev acc
    | Some tok ->
        incr tok_count;
        aux ((tok, loc_func !tok_count) :: acc) in
  aux []

let rotten_script ~fname statement =
  (* XXX terribly inefficient: the same script is read several times ... *)
  let lexer = CicNotationLexer.level2_ast_lexer in
  let token_stream, loc_func =
    lexer.Token.tok_func (Obj.magic (Ulexing.from_utf8_string statement)) in
  let tokens = flush_token_stream (token_stream, loc_func) in
  let target_token, target_pos =
    let rec sanitize_tokens acc = function
      | [] -> List.rev acc
      | (("IDENT",
          ("theorem" | "definition" | "lemma" | "record" | "inductive")), _)
        :: (("IDENT", _), _) :: tl ->
          (* avoid rottening of object names *)
          sanitize_tokens acc tl
      | (("SYMBOL", ("∀" | "λ" | "Π")), _) :: (("IDENT", _), _) :: tl ->
          (* avoid rottening of binders *)
          let rec remove_args = function
            | (("SYMBOL", ","), _) :: (("IDENT", _), _) :: tl ->
                remove_args tl
            | tl -> tl in
          sanitize_tokens acc (remove_args tl)
      | (("SYMBOL", "⇒"), _) as hd :: tl ->
          (* avoid rottening of constructor names in pattern matching *)
          let rec remove_until_branch_start = function
            | (("SYMBOL", ("|" | "[")), _) :: tl -> tl
            | hd :: tl -> remove_until_branch_start tl
            | [] -> [] in
          sanitize_tokens (hd :: remove_until_branch_start acc) tl
      | hd :: tl -> (* every other identfier can be rottened! *)
          sanitize_tokens (hd :: acc) tl in
    let idents =
      List.filter (function (("IDENT", _), _) -> true | _ -> false)
        (sanitize_tokens [] tokens) in
    List.nth idents (Random.int (List.length idents))
  in
  let start_pos, end_pos =  (* positions in bytecount *)
    Glib.Utf8.offset_to_pos statement 0 (Stdpp.first_pos target_pos),
    Glib.Utf8.offset_to_pos statement 0 (Stdpp.last_pos target_pos) in
  let statement' =
    if !add_ident then
      String.sub statement 0 start_pos
      ^ "O "
      ^ String.sub statement start_pos (String.length statement - start_pos)
    else
      String.sub statement 0 start_pos
      ^ "O"
      ^ String.sub statement end_pos (String.length statement - end_pos)
  in
  let script = HExtlib.input_file fname in
  let matches =
    let rex =
      Pcre.regexp ~flags:[`DOTALL]
        (sprintf "^(.*)(%s)(.*)$" (Pcre.quote statement)) in
    try
      Pcre.extract ~rex script
    with Not_found -> assert false
  in
  let trailer = (* trailing comment with machine parseable error location *)
    let preamble_len = Glib.Utf8.length matches.(1) in
    sprintf "\n(*\nerror-at: %d-%d\n*)\n"
      (preamble_len + Stdpp.first_pos target_pos)
      (preamble_len + Stdpp.first_pos target_pos + error_token_len) in
  let script' =
    sprintf "%s%s%s%s" matches.(1) statement' matches.(3) trailer in
  let md5 = Digest.to_hex (Digest.string script') in
  HExtlib.output_file
    ~filename:(sprintf "%s.%s.rottened" fname md5)
    ~text:script'

let grep () =
  let recursive = ref false in
  let spec = [
    "-r", Arg.Set recursive, "enable directory recursion";
  ] in
  MatitaInit.add_cmdline_spec spec;
  MatitaInit.initialize_all ();
  let include_paths =
    Helm_registry.get_list Helm_registry.string "matita.includes" in
  let status =
    CicNotation2.load_notation ~include_paths
      BuildTimeConf.core_notation_script in
  let path =
    match Helm_registry.get_list Helm_registry.string "matita.args" with
    | [ path ] -> path
    | _ -> MatitaInit.die_usage () in
  let grep_fun =
    if !recursive then
      (fun dirname ->
        let sane_statements =
          GrafiteWalker.rgrep_statement ~status ~dirname has_toplevel_term in
        List.iter (fun (fname, statement) -> rotten_script ~fname statement)
          sane_statements)
    else
      (fun fname ->
        let sane_statements =
          GrafiteWalker.grep_statement ~status ~fname has_toplevel_term in
        List.iter (fun statement -> rotten_script ~fname statement)
          sane_statements)
  in
  grep_fun path

let handle_localized_exns f arg =
  try
    f arg
  with HExtlib.Localized (loc, exn) ->
    let loc_begin, loc_end = HExtlib.loc_of_floc loc in
    eprintf "Error at %d-%d: %s\n%!" loc_begin loc_end (Printexc.to_string exn)

let _ =
  Random.self_init ();
  handle_localized_exns grep ()

