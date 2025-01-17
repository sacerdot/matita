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

exception Error of int * int * string

module StringSet = Set.Make(String)

(* Lexer *)
let number = [%sedlex.regexp? (Plus xml_digit)]
let utf8_blank = [%sedlex.regexp? " " | "\r\n" | "\n" | "\t" | 160 (* this is a nbsp *)]
let percentage = [%sedlex.regexp?
  ('-' | ""),(Plus ( '0' .. '9' )),'%' ]
let floatwithunit = [%sedlex.regexp?
  ('-' | ""),(Plus ( '0' .. '9' )),".",(Plus ( '0' .. '9' )),((Plus ( 'a' .. 'z' )) | "" ) ]
let color =  [%sedlex.regexp? "#",( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ),( '0' .. '9' | 'a' .. 'f' |
'A' .. 'F' ),( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ),( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ),
( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ), ( '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' ) ]

  (* ZACK: breaks unicode's binder followed by an ascii letter without blank *)
(* let ident_letter = [%sedlex.regexp? xml_letter ] *)

let ident_letter = [%sedlex.regexp? ( 'a' .. 'z' | 'A' .. 'Z' )]

  (* must be in sync with "is_ligature_char" below *)
let ligature_char = [%sedlex.regexp? (Chars "'`~!?@*()[]<>-+=|:;.,/\"" ) ]
let ligature = [%sedlex.regexp? ligature_char,(Plus ligature_char) ]

let we_proved = [%sedlex.regexp? "we",(Plus utf8_blank),"proved"]
let we_have = [%sedlex.regexp? "we",(Plus utf8_blank),"have"]
let let_rec = [%sedlex.regexp? "let",(Plus utf8_blank),"rec" ]
let let_corec = [%sedlex.regexp? "let",(Plus utf8_blank),"corec"]
let ident_decoration = [%sedlex.regexp? '\'' | '?' | '`']
let ident_cont = [%sedlex.regexp? ident_letter | xml_digit | '_']
let ident_start = [%sedlex.regexp? ident_letter]
let ident = [%sedlex.regexp? ident_letter,(Star ident_cont),Star ident_decoration]
let variable_ident = [%sedlex.regexp? '_','_',number]
let pident = [%sedlex.regexp? '_',ident]

let tex_token = [%sedlex.regexp? '\\',ident]

let delim_begin = [%sedlex.regexp? "\\["]
let delim_end = [%sedlex.regexp? "\\]"]

let qkeyword = [%sedlex.regexp? "'",( ident | pident ),"'"]

let implicit = [%sedlex.regexp? '?']
let placeholder = [%sedlex.regexp? '%']
let meta = [%sedlex.regexp? implicit,number]

let csymbol = [%sedlex.regexp? '\'',ident]

let begin_group = [%sedlex.regexp? "@{" | "${"]
let end_group = [%sedlex.regexp? '}']
let wildcard = [%sedlex.regexp? "$_"]
let ast_ident = [%sedlex.regexp? "@",ident]
let ast_csymbol = [%sedlex.regexp? "@",csymbol]
let meta_ident = [%sedlex.regexp? "$",ident]
let meta_anonymous = [%sedlex.regexp? "$_"]
let qstring = [%sedlex.regexp? '"',(Star (Compl '"')),'"']

let begincomment = [%sedlex.regexp? "(**",utf8_blank]
let beginnote = [%sedlex.regexp? "(*"]
let endcomment = [%sedlex.regexp? "*)"]
(* let comment_char = [%sedlex.regexp? (Compl '*') | '*',(Compl ')')]
let note = [%sedlex.regexp? "|+",((Compl '*') | "**"),(Star comment_char),"+|"] *)

let level1_layouts = 
  [ "sub"; "sup";
    "below"; "above";
    "over"; "atop"; "frac";
    "sqrt"; "root"; "mstyle" ; "mpadded"; "maction"

  ]

let level1_keywords =
  [ "hbox"; "hvbox"; "hovbox"; "vbox";
    "break";
    "list0"; "list1"; "sep";
    "opt";
    "term"; "ident"; "number";
  ] @ level1_layouts

let level2_meta_keywords =
  [ "if"; "then"; "elCicNotationParser.se";
    "fold"; "left"; "right"; "rec";
    "fail";
    "default";
    "anonymous"; "ident"; "number"; "term"; "fresh"
  ]

  (* (string, int) Hashtbl.t, with multiple bindings.
   * int is the unicode codepoint *)
let ligatures = Hashtbl.create 23

let _ =
  List.iter
    (fun (ligature, symbol) -> Hashtbl.add ligatures ligature symbol)
    [ ("->", "→"(*<:unicode<to>>*));   ("=>", "⇒"(*<:unicode<Rightarrow>>*));
      (":=", "≝"(*<:unicode<def>>*));
    ]

let uri_step = [%sedlex.regexp?  Plus ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '\'')]

let uri = [%sedlex.regexp? 
  ("cic:/" | "theory:/"),                    (* schema *)
(*   ident ('/' ident),*                     |+ path +| *)
  uri_step,(Star ('/',uri_step)),            (* path *)
  (Plus ('.',ident)),                        (* ext *)
  (Opt ("#xpointer(",number,(Plus ('/',number)),")"))  (* xpointer *)
]

let nreference = [%sedlex.regexp? 
  "cic:/",                            (* schema *)
  uri_step,(Star ('/',uri_step)),     (* path *)
  '#',
  ( "dec"
  | "def",":",number,""
  | "fix",":",number,":",number,":",number
  | "cfx",":",number
  | "ind",":",number,":",number,":",number
  | "con",":",number,":",number,":",number
  ) (* (Plus ext),reference *)
]

let error lexbuf msg =
  let begin_cnum, end_cnum = Sedlexing.loc lexbuf in
  raise (Error (begin_cnum, end_cnum, msg))
let error_at_end lexbuf msg =
  let begin_cnum, end_cnum = Sedlexing.loc lexbuf in
  raise (Error (begin_cnum, end_cnum, msg))

let return_with_loc token begin_cnum end_cnum =
  let flocation = HExtlib.floc_of_loc (begin_cnum,end_cnum) in
   token, flocation

let return lexbuf token =
  let begin_cnum, end_cnum = Sedlexing.loc lexbuf in
    return_with_loc token begin_cnum end_cnum

let return_lexeme lexbuf name = return lexbuf (name, Sedlexing.Utf8.lexeme lexbuf)

let return_symbol lexbuf s = return lexbuf ("SYMBOL", s)
let return_eoi lexbuf = return lexbuf ("EOI", "")

let remove_quotes s = String.sub s 1 (String.length s - 2)

let mk_lexer token =
  let tok_func stream =
(*     let lexbuf = Sedlexing.Utf8.from_stream stream in *)
(** XXX Obj.magic rationale.
 * The problem.
 *  camlp5 constraints the tok_func field of Token.glexer to have type:
 *    Stream.t char -> (Stream.t 'te * flocation_function)
 *  In order to use ulex we have (in theory) to instantiate a new lexbuf each
 *  time a char Stream.t is passed, destroying the previous lexbuf which may
 *  have consumed a character from the old stream which is lost forever :-(
 * The "solution".
 *  Instead of passing to camlp5 a char Stream.t we pass a lexbuf, casting it to
 *  char Stream.t with Obj.magic where needed.
 *)
    let lexbuf = Obj.magic stream in
    Token.make_stream_and_location
      (fun () ->
        try
          token lexbuf
        with
        | Sedlexing.MalFormed -> error_at_end lexbuf "Unexpected character"
        | Sedlexing.InvalidCodepoint p ->
            error_at_end lexbuf (sprintf "Invalid code point: %d" p))
  in
  {
    Token.tok_func = tok_func;
    Token.tok_using = (fun _ -> ());
    Token.tok_removing = (fun _ -> ()); 
    Token.tok_match = Token.default_match;
    Token.tok_text = Token.lexer_text;
    Token.tok_comm = None;
    Token.kwds = Hashtbl.create 301;
  }

let expand_macro lexbuf =
  let macro =
    Sedlexing.Utf8.sub_lexeme lexbuf 1 (Sedlexing.lexeme_length lexbuf - 1)
  in
  try
    ("SYMBOL", Utf8Macro.expand macro)
  with Utf8Macro.Macro_not_found _ -> 
(* FG: unexpanded TeX macros are terminated by a space for rendering *)     
     "SYMBOL", (Sedlexing.Utf8.lexeme lexbuf ^ " ")

let remove_quotes s = String.sub s 1 (String.length s - 2)
let remove_left_quote s = String.sub s 1 (String.length s - 1)

let rec level2_pattern_token_group counter buffer lexbuf =
  match%sedlex lexbuf with
  | end_group -> 
      if (counter > 0) then
	Buffer.add_string buffer (Sedlexing.Utf8.lexeme lexbuf) ;
      snd (Sedlexing.loc lexbuf)
  | begin_group -> 
      Buffer.add_string buffer (Sedlexing.Utf8.lexeme lexbuf) ;
      ignore (level2_pattern_token_group (counter + 1) buffer lexbuf) ;
      level2_pattern_token_group counter buffer lexbuf
  | any -> 
      Buffer.add_string buffer (Sedlexing.Utf8.lexeme lexbuf) ;
      level2_pattern_token_group counter buffer lexbuf
  | _ -> assert false

let read_unparsed_group token_name lexbuf =
  let buffer = Buffer.create 16 in
  let begin_cnum, _ = Sedlexing.loc lexbuf in
  let end_cnum = level2_pattern_token_group 0 buffer lexbuf in
    return_with_loc (token_name, Buffer.contents buffer) begin_cnum end_cnum

let handle_keywords lexbuf k name = 
  let s = Sedlexing.Utf8.lexeme lexbuf in
  if k s then
	    return lexbuf ("", s)
	  else
	    return lexbuf (name, s)
;;

let rec level2_meta_token lexbuf =
  match%sedlex lexbuf with
  | Plus utf8_blank -> level2_meta_token lexbuf
  | ident ->
      handle_keywords lexbuf (fun x -> List.mem x level2_meta_keywords) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Sedlexing.Utf8.lexeme lexbuf)
  | pident ->
      handle_keywords lexbuf (fun x -> List.mem x level2_meta_keywords) "PIDENT"
  | "@{" -> read_unparsed_group "UNPARSED_AST" lexbuf
  | ast_ident ->
      return lexbuf ("UNPARSED_AST",
        remove_left_quote (Sedlexing.Utf8.lexeme lexbuf))
  | ast_csymbol ->
      return lexbuf ("UNPARSED_AST",
        remove_left_quote (Sedlexing.Utf8.lexeme lexbuf))
  | eof -> return_eoi lexbuf
  | _ -> assert false (*raise Sedlexing.MalFormed (*CSC: ???*)*)

let rec comment_token acc depth lexbuf =
  match%sedlex lexbuf with
  | beginnote ->
      let acc = acc ^ Sedlexing.Utf8.lexeme lexbuf in
      comment_token acc (depth + 1) lexbuf
  | endcomment ->
      let acc = acc ^ Sedlexing.Utf8.lexeme lexbuf in
      if depth = 0
      then acc
      else comment_token acc (depth - 1) lexbuf
  | any ->
      let acc = acc ^ Sedlexing.Utf8.lexeme lexbuf in
      comment_token acc depth lexbuf
  | _ -> assert false

  (** @param k continuation to be invoked when no ligature has been found *)
let ligatures_token k lexbuf =
  match%sedlex lexbuf with
  | ligature ->
      let lexeme = Sedlexing.Utf8.lexeme lexbuf in
      (match List.rev (Hashtbl.find_all ligatures lexeme) with
      | [] -> (* ligature not found, rollback and try default lexer *)
          Sedlexing.rollback lexbuf;
          k lexbuf
      | default_lig :: _ -> (* ligatures found, use the default one *)
          return_symbol lexbuf default_lig)
  | eof -> return_eoi lexbuf
  | _ ->  (* not a ligature, rollback and try default lexer *)
      Sedlexing.rollback lexbuf; (*CSC: is it necessary/correct? nothing has been matched... *)
      k lexbuf

let rec level2_ast_token status lexbuf =
  match%sedlex lexbuf with
  | let_rec -> return lexbuf ("LETREC","")
  | let_corec -> return lexbuf ("LETCOREC","")
  | we_proved -> return lexbuf ("WEPROVED","")
  | we_have -> return lexbuf ("WEHAVE","")
  | Plus utf8_blank -> ligatures_token (level2_ast_token status) lexbuf
  | meta ->
     let s = Sedlexing.Utf8.lexeme lexbuf in
      return lexbuf ("META", String.sub s 1 (String.length s - 1))
  | implicit -> return lexbuf ("IMPLICIT", "")
  | placeholder -> return lexbuf ("PLACEHOLDER", "")
  | ident -> handle_keywords lexbuf (fun x -> StringSet.mem x status) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Sedlexing.Utf8.lexeme lexbuf)
  | pident -> handle_keywords lexbuf (fun x -> StringSet.mem x status) "PIDENT"
  | number -> return lexbuf ("NUMBER", Sedlexing.Utf8.lexeme lexbuf)
  | tex_token -> return lexbuf (expand_macro lexbuf)
  | nreference -> return lexbuf ("NREF", Sedlexing.Utf8.lexeme lexbuf)
  | uri -> return lexbuf ("URI", Sedlexing.Utf8.lexeme lexbuf)
  | qstring ->
      return lexbuf ("QSTRING", remove_quotes (Sedlexing.Utf8.lexeme lexbuf))
  | csymbol ->
      return lexbuf ("CSYMBOL", remove_left_quote (Sedlexing.Utf8.lexeme lexbuf))
  | "${" -> read_unparsed_group "UNPARSED_META" lexbuf
  | "@{" -> read_unparsed_group "UNPARSED_AST" lexbuf
  | '(' -> return lexbuf ("LPAREN", "")
  | ')' -> return lexbuf ("RPAREN", "")
  | meta_ident ->
      return lexbuf ("UNPARSED_META",
        remove_left_quote (Sedlexing.Utf8.lexeme lexbuf))
  | meta_anonymous -> return lexbuf ("UNPARSED_META", "anonymous")
  | beginnote -> 
      let _comment = comment_token (Sedlexing.Utf8.lexeme lexbuf) 0 lexbuf in
(*       let comment =
        Sedlexing.Utf8.sub_lexeme lexbuf 2 (Sedlexing.lexeme_length lexbuf - 4)
      in
      return lexbuf ("NOTE", comment) *)
      ligatures_token (level2_ast_token status) lexbuf
  | begincomment ->
      return lexbuf ("BEGINCOMMENT","")
  | endcomment -> return lexbuf ("ENDCOMMENT","")
  | eof -> return_eoi lexbuf
  | any -> return_symbol lexbuf (Sedlexing.Utf8.lexeme lexbuf)
  | _ -> assert false

and level1_pattern_token lexbuf =
  match%sedlex lexbuf with
  | Plus utf8_blank -> ligatures_token level1_pattern_token lexbuf
  | number -> return lexbuf ("NUMBER", Sedlexing.Utf8.lexeme lexbuf)
  | ident ->handle_keywords lexbuf (fun x -> List.mem x level1_keywords) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Sedlexing.Utf8.lexeme lexbuf)
  | pident->handle_keywords lexbuf (fun x->List.mem x level1_keywords) "PIDENT" 
  | color -> return lexbuf ("COLOR", Sedlexing.Utf8.lexeme lexbuf)
  | percentage -> 
      return lexbuf ("PERCENTAGE", Sedlexing.Utf8.lexeme lexbuf)
  | floatwithunit -> 
      return lexbuf ("FLOATWITHUNIT", Sedlexing.Utf8.lexeme lexbuf)
  | tex_token -> return lexbuf (expand_macro lexbuf)
  | qkeyword ->
      return lexbuf ("QKEYWORD", remove_quotes (Sedlexing.Utf8.lexeme lexbuf))
  | '(' -> return lexbuf ("LPAREN", "")
  | ')' -> return lexbuf ("RPAREN", "")
  | eof -> return_eoi lexbuf
  | any -> return_symbol lexbuf (Sedlexing.Utf8.lexeme lexbuf)
  | _ -> assert false

let level1_pattern_token = ligatures_token level1_pattern_token
let level2_ast_token status = ligatures_token (level2_ast_token status)

(* API implementation *)
type lexers = {
        level1_pattern_lexer : (string * string) Token.glexer;
        level2_ast_lexer : (string * string) Token.glexer;
        level2_meta_lexer : (string * string) Token.glexer
}

let mk_lexers keywords = 
  let initial_keywords = 
   [ "CProp"; "Prop"; "Type"; "Set"; "let"; "match";
   "with"; "in"; "and"; "to"; "as"; "on"; "return"; "done" ]
  in
  let status = 
    List.fold_right StringSet.add (initial_keywords @ keywords) StringSet.empty 
  in 
  {
        level1_pattern_lexer = mk_lexer level1_pattern_token;
        level2_ast_lexer = mk_lexer (level2_ast_token status);
        level2_meta_lexer = mk_lexer level2_meta_token
  }
;;
