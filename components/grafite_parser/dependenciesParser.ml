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

exception UnableToInclude of string

  (* statements meaningful for matitadep *)
type dependency =
  | IncludeDep of string
  | UriDep of NUri.uri
  | InlineDep of string

let pp_dependency = function
  | IncludeDep str -> "include \"" ^ str ^ "\""
  | UriDep uri -> "uri \"" ^ NUri.string_of_uri uri ^ "\""
  | InlineDep str -> "inline \"" ^ str ^ "\"" 

let parse_dependencies lexbuf = 
  let tok_stream,_ =
    (CicNotationLexer.level2_ast_lexer ()).Token.tok_func (Obj.magic lexbuf)
  in
  let rec parse acc = 
   let continue, acc =
     try
      (parser
      | [< '("QSTRING", s) >] ->
          (* because of alias id qstring = qstring :-( *)
          if String.sub s 0 5 <> "cic:/" then true,acc
          else
            true, (UriDep (NUri.uri_of_string s) :: acc)
      | [< '("URI", u) >] ->
          true, (UriDep (NUri.uri_of_string u) :: acc)
      | [< '("IDENT", "include"); '("QSTRING", fname) >] ->
          true, (IncludeDep fname :: acc)
      | [< '("IDENT", "include"); '("IDENT", "source"); '("QSTRING", fname) >] ->
          true, (IncludeDep fname :: acc)
      | [< '("IDENT", "include'"); '("QSTRING", fname) >] ->
          true, (IncludeDep fname :: acc)
      | [< '("IDENT", "inline"); '("QSTRING", fname) >] ->
          true, (InlineDep fname :: acc)
      | [< '("EOI", _) >] -> false, acc
      | [< 'tok >] -> true, acc
      | [<  >] -> false, acc) tok_stream
     with
        Stream.Error _ -> false, acc
      | CicNotationLexer.Error _ -> true, acc
   in
    if continue then parse acc else acc
  in
  List.rev (parse [])

let deps_of_file ma_file =
 try
   let ic = open_in ma_file in
   let istream = Ulexing.from_utf8_channel ic in
   let dependencies = parse_dependencies istream in
   close_in ic;
   dependencies
 with End_of_file -> []
;;
