(* Copyright (C) 2004, HELM Team.
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

type npattern = 
 NotationPt.term option * (string * NotationPt.term) list * NotationPt.term option

type auto_params = NotationPt.term list option * (string*string) list

type ntactic =
   | NApply of loc * NotationPt.term
   | NSmartApply of loc * NotationPt.term
   | NAssert of loc * ((string * [`Decl of NotationPt.term | `Def of NotationPt.term * NotationPt.term]) list * NotationPt.term) list
   | NCases of loc * NotationPt.term * npattern  
   | NCase1 of loc * string
   | NChange of loc * npattern * NotationPt.term
   | NConstructor of loc * int option * NotationPt.term list
   | NCut of loc * NotationPt.term
(* | NDiscriminate of loc * NotationPt.term
   | NSubst of loc * NotationPt.term *)
   | NDestruct of loc * string list option * string list
   | NElim of loc * NotationPt.term * npattern  
   | NGeneralize of loc * npattern
   | NId of loc
   | NIntro of loc * string
   | NIntros of loc * string list
   | NInversion of loc * NotationPt.term * npattern  
   | NLApply of loc * NotationPt.term
   | NLetIn of loc * npattern * NotationPt.term * string
   | NReduce of loc * [ `Normalize of bool | `Whd of bool ] * npattern
   | NRewrite of loc * direction * NotationPt.term * npattern
   | NAuto of loc * auto_params
   | NDot of loc
   | NSemicolon of loc
   | NBranch of loc
   | NShift of loc
   | NPos of loc * int list
   | NPosbyname of loc * string
   | NWildcard of loc
   | NMerge of loc
   | NSkip of loc
   | NFocus of loc * int list
   | NUnfocus of loc
   | NTry of loc * ntactic
   | NAssumption of loc
   | NRepeat of loc * ntactic
   | NBlock of loc * ntactic list

type nmacro =
  | NCheck of loc * NotationPt.term
  | Screenshot of loc * string
  | NAutoInteractive of loc * auto_params
  | NIntroGuess of loc

(** To be increased each time the command type below changes, used for "safe"
 * marshalling *)
let magic = 35

type command =
  | Include of loc * string * unit * string
  | Set of loc * string * string
  | Print of loc * string

type ncommand =
  | UnificationHint of loc * NotationPt.term * int (* term, precedence *)
  | NObj of loc * NotationPt.term NotationPt.obj
  | NDiscriminator of loc * NotationPt.term
  | NInverter of loc * string * NotationPt.term * bool list option * NotationPt.term option
  | NUnivConstraint of loc * NUri.uri * NUri.uri
  | NCopy of loc * string * NUri.uri * (NUri.uri * NUri.uri) list
  | NCoercion of loc * string *
      NotationPt.term * NotationPt.term *
      (string * NotationPt.term) * NotationPt.term
  | NQed of loc

type code =
  | Command of loc * command
  | NCommand of loc * ncommand
  | NMacro of loc * nmacro 
  | NTactic of loc * ntactic list
             
type comment =
  | Note of loc * string
  | Code of loc * code
             
type statement =
  | Executable of loc * code
  | Comment of loc * comment
