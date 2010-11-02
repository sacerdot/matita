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

open LexiconAst

class type g_status =
 object ('self)
  inherit Interpretations.g_status
  inherit TermContentPres.g_status
  inherit CicNotationParser.g_status
 end

class status =
 object (self)
  inherit Interpretations.status
  inherit TermContentPres.status
  inherit CicNotationParser.status
  method set_notation_status
   : 'status. #g_status as 'status -> 'self
      = fun o -> ((self#set_interp_status o)#set_content_pres_status o)#set_notation_parser_status o
 end

let process_notation status st =
  match st with
  | Notation (loc, dir, l1, associativity, precedence, l2) ->
      let l1 = 
        CicNotationParser.check_l1_pattern
         l1 (dir = Some `RightToLeft) precedence associativity
      in
      let status =
        if dir <> Some `RightToLeft then
          CicNotationParser.extend status l1 
            (fun env loc ->
              NotationPt.AttributedTerm
               (`Loc loc,TermContentPres.instantiate_level2 env l2)) 
        else status
      in
      let status =
        if dir <> Some `LeftToRight then
         let status = TermContentPres.add_pretty_printer status l2 l1 in
          status
        else
          status
      in
       status
  | Interpretation (loc, dsc, l2, l3) -> 
      Interpretations.add_interpretation status dsc l2 l3
  | st -> status

