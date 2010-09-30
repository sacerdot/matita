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

open LexiconAst

let pp_l1_pattern = CicNotationPp.pp_term
let pp_l2_pattern = CicNotationPp.pp_term

let pp_alias = function
  | Ident_alias (id, uri) -> sprintf "alias id \"%s\" = \"%s\"." id uri
  | Symbol_alias (symb, instance, desc) ->
      sprintf "alias symbol \"%s\" %s= \"%s\"."
        symb
        (if instance=0 then "" else "(instance "^ string_of_int instance ^ ") ")
        desc
  | Number_alias (instance,desc) ->
      sprintf "alias num (instance %d) = \"%s\"." instance desc
  
let pp_associativity = function
  | Gramext.LeftA -> "left associative"
  | Gramext.RightA -> "right associative"
  | Gramext.NonA -> "non associative"

let pp_precedence i = sprintf "with precedence %d" i

let pp_argument_pattern = function
  | CicNotationPt.IdentArg (eta_depth, name) ->
      let eta_buf = Buffer.create 5 in
      for i = 1 to eta_depth do
        Buffer.add_string eta_buf "\\eta."
      done;
      sprintf "%s%s" (Buffer.contents eta_buf) name

let pp_interpretation dsc symbol arg_patterns cic_appl_pattern = 
  sprintf "interpretation \"%s\" '%s %s = %s."
    dsc symbol
    (String.concat " " (List.map pp_argument_pattern arg_patterns))
    (CicNotationPp.pp_cic_appl_pattern cic_appl_pattern)
 
let pp_dir_opt = function
  | None -> ""
  | Some `LeftToRight -> "> "
  | Some `RightToLeft -> "< "

let pp_notation dir_opt l1_pattern assoc prec l2_pattern = 
  sprintf "notation %s\"%s\" %s %s for %s."
    (pp_dir_opt dir_opt)
    (pp_l1_pattern l1_pattern)
    (pp_associativity assoc)
    (pp_precedence prec)
    (pp_l2_pattern l2_pattern)
    
let pp_command = function
  | Include (_,_,mode,path) -> (* not precise, since path is absolute *)
      if mode = WithPreferences then
        "include \"" ^ path ^ "\"."
      else
        "include' \"" ^ path ^ "\"."
  | Alias (_,s) -> pp_alias s
  | Interpretation (_, dsc, (symbol, arg_patterns), cic_appl_pattern) ->
      pp_interpretation dsc symbol arg_patterns cic_appl_pattern
  | Notation (_, dir_opt, l1_pattern, assoc, prec, l2_pattern) ->
      pp_notation dir_opt l1_pattern assoc prec l2_pattern
