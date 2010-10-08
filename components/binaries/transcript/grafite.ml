(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

module T = Types
module O = Options

module UM = UriManager
module NP = NotationPp
module GP = GrafiteAstPp
module G  = GrafiteAst
module H  = HExtlib

let floc = H.dummy_floc

let out_verbatim och s =
   Printf.fprintf och "%s" s

let out_comment och s =
   let s = if s <> "" && s.[0] = '*' then "#" ^ s else s in 
   Printf.fprintf och "%s%s%s\n\n" "(*" s "*)"

let out_unexported och head s =
   let s = Printf.sprintf " %s\n%s\n" head s in
   out_comment och s

let out_line_comment och s =
   let l = 70 - String.length s in
   let l = if l < 0 then 0 else l in
   let s = Printf.sprintf " %s %s" s (String.make l '*') in
   out_comment och s

let out_preamble och (path, lines) =
   let ich = open_in path in
   let rec print i =
      if i > 0 then 
         let s = input_line ich in
         begin Printf.fprintf och "%s\n" s; print (pred i) end
   in 
   print lines;
   out_line_comment och "This file was automatically generated: do not edit"
      
let out_command och cmd =
   let term_pp = NP.pp_term in
   let lazy_term_pp = NP.pp_term in
   let obj_pp = NP.pp_obj NP.pp_term in
   let s = GP.pp_statement ~map_unicode_to_tex:false ~term_pp ~lazy_term_pp ~obj_pp cmd in
   Printf.fprintf och "%s\n\n" s

let command_of_obj obj =
   G.Executable (floc, G.Command (floc, obj))

let command_of_macro macro =
   G.Executable (floc, G.Macro (floc, macro))

let require moo value =
   command_of_obj (G.Include (floc, moo, `OldAndNew, value ^ ".ma"))

let coercion value =
   command_of_obj (G.Coercion (floc, UM.uri_of_string value, true, 0, 0))

let inline kind uri prefix flavour params =
    let params = match prefix with
       | ""     -> params
       | prefix -> G.IPPrefix prefix :: params
    in
    let params = match flavour with
       | None         -> params
       | Some flavour -> G.IPAs flavour :: params
    in
    let params = match kind with
       | T.Declarative -> params
       | T.Procedural  -> G.IPProcedural :: params 
    in    
    command_of_macro (G.Inline (floc, uri, params))

let out_alias och name uri =
   Printf.fprintf och "alias id \"%s\" = \"%s\".\n\n" name uri

let check och src =
   if Http_getter.exists ~local:false src then () else
   let msg = "UNAVAILABLE OBJECT: " ^ src in
   out_line_comment och msg;
   prerr_endline msg

let commit kind och items =
   let trd (_, _, x) = x in
   let commit = function
      | T.Heading heading       -> out_preamble och heading
      | T.Line line             ->
         if !O.comments then out_line_comment och line
      | T.Include (moo, script) -> out_command och (require moo script)
      | T.Coercion specs        -> 
         if !O.comments then out_unexported och "COERCION" (snd specs)
      | T.Notation specs        -> 
         if !O.comments then out_unexported och "NOTATION" (snd specs) (**)
      | T.Inline (_, T.Var, src, _, _, _) ->
         if !O.comments then out_unexported och "UNEXPORTED" src
(* FG: we do not export variables because we cook the other objects         
 *	 let name = UriManager.name_of_uri (UriManager.uri_of_string src) in
 *       out_alias och name src
 *)
      | T.Inline (_, _, src, pre, fl, params) -> 
         if !O.getter then check och src; 
	 out_command och (inline kind src pre fl params)
      | T.Section specs     -> 
         if !O.comments then out_unexported och "UNEXPORTED" (trd specs)
      | T.Comment comment   -> 
         if !O.comments then out_comment och comment
      | T.Unexport unexport -> 
         if !O.comments then out_unexported och "UNEXPORTED" unexport 
      | T.Verbatim verbatim -> out_verbatim och verbatim
      | T.Discard _         -> ()
   in 
   List.iter commit (List.rev items)

let string_of_inline_kind = function
   | T.Con -> ".con"
   | T.Var -> ".var"
   | T.Ind -> ".ind"
