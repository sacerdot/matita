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

type direction = [ `LeftToRight | `RightToLeft ]

type loc = Stdpp.location

type alias_spec =
  | Ident_alias of string * string        (* identifier, uri *)
  | Symbol_alias of string * int * string (* name, instance no, description *)
  | Number_alias of int * string          (* instance no, description *)

(** To be increased each time the command type below changes, used for "safe"
 * marshalling *)
let magic = 6

type inclusion_mode = WithPreferences | WithoutPreferences (* aka aliases *)

type command =
  | Include of loc * string * inclusion_mode * string (* _,buri,_,path *)
  | Alias of loc * alias_spec
      (** parameters, name, type, fields *) 
  | Notation of loc * direction option * NotationPt.term * Gramext.g_assoc *
      int * NotationPt.term
      (* direction, l1 pattern, associativity, precedence, l2 pattern *)
  | Interpretation of loc *
      string * (string * NotationPt.argument_pattern list) *
        NotationPt.cic_appl_pattern
      (* description (i.e. id), symbol, arg pattern, appl pattern *)

(* composed magic: term + command magics. No need to change this value *)
let magic = magic + 10000 * NotationPt.magic

let description_of_alias =
 function
    Ident_alias (_,desc)
  | Symbol_alias (_,_,desc)
  | Number_alias (_,desc) -> desc
