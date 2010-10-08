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

type ('term, 'lazy_term, 'ident) pattern =
  'lazy_term option * ('ident * 'term) list * 'term option

type npattern = 
 NotationPt.term option * (string * NotationPt.term) list * NotationPt.term option

type 'lazy_term reduction =
  [ `Normalize
  | `Simpl
  | `Unfold of 'lazy_term option
  | `Whd ]

type 'ident intros_spec = int option * 'ident option list

type 'term auto_params = 'term list option * (string*string) list

type 'term just =
 [ `Term of 'term
 | `Auto of 'term auto_params ]

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
   | NAuto of loc * NotationPt.term auto_params
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

type ('term, 'lazy_term, 'reduction, 'ident) tactic =
  (* Higher order tactics (i.e. tacticals) *)
  | Do of loc * int * ('term, 'lazy_term, 'reduction, 'ident) tactic
  | Repeat of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic
  | Seq of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic list
      (* sequential composition *)
  | Then of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic *
      ('term, 'lazy_term, 'reduction, 'ident) tactic list
  | First of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic list
      (* try a sequence of loc * tactic until one succeeds, fail otherwise *)
  | Try of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic
      (* try a tactic and mask failures *)
  | Solve of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic list
  | Progress of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic
  (* Real tactics *)
  | Absurd of loc * 'term
  | Apply of loc * 'term
  | ApplyRule of loc * 'term
  | ApplyP of loc * 'term (* apply for procedural reconstruction *)
  | ApplyS of loc * 'term * 'term auto_params
  | Assumption of loc
  | AutoBatch of loc * 'term auto_params
  | Cases of loc * 'term * ('term, 'lazy_term, 'ident) pattern *
             'ident intros_spec
  | Change of loc * ('term, 'lazy_term, 'ident) pattern * 'lazy_term
  | Clear of loc * 'ident list
  | ClearBody of loc * 'ident
  | Compose of loc * 'term * 'term option * int * 'ident intros_spec
  | Constructor of loc * int
  | Contradiction of loc
  | Cut of loc * 'ident option * 'term
  | Decompose of loc * 'ident option list
  | Demodulate of loc * 'term auto_params
  | Destruct of loc * 'term list option
  | Elim of loc * 'term * 'term option * ('term, 'lazy_term, 'ident) pattern *
	    'ident intros_spec
  | ElimType of loc * 'term * 'term option * 'ident intros_spec
  | Exact of loc * 'term
  | Exists of loc
  | Fail of loc
  | Fold of loc * 'reduction * 'lazy_term * ('term, 'lazy_term, 'ident) pattern
  | Fourier of loc
  | FwdSimpl of loc * string * 'ident option list
  | Generalize of loc * ('term, 'lazy_term, 'ident) pattern * 'ident option
  | IdTac of loc
  | Intros of loc * 'ident intros_spec
  | Inversion of loc * 'term
  | LApply of loc * bool * int option * 'term list * 'term * 'ident option
  | Left of loc
  | LetIn of loc * 'term * 'ident
  | Reduce of loc * 'reduction * ('term, 'lazy_term, 'ident) pattern 
  | Reflexivity of loc
  | Replace of loc * ('term, 'lazy_term, 'ident) pattern * 'lazy_term
  | Rewrite of loc * direction * 'term *
      ('term, 'lazy_term, 'ident) pattern * 'ident option list
  | Right of loc
  | Ring of loc
  | Split of loc
  | Symmetry of loc
  | Transitivity of loc * 'term
  (* Declarative language *)
  | Assume of loc * 'ident * 'term
  | Suppose of loc * 'term *'ident * 'term option
  | By_just_we_proved of loc * 'term just *
     'term * 'ident option * 'term option
  | We_need_to_prove of loc * 'term * 'ident option * 'term option
  | Bydone of loc * 'term just
  | We_proceed_by_induction_on of loc * 'term * 'term
  | We_proceed_by_cases_on of loc * 'term * 'term
  | Byinduction of loc * 'term * 'ident
  | Thesisbecomes of loc * 'term
  | Case of loc * string * (string * 'term) list 
  | ExistsElim of loc * 'term just * 'ident * 'term * 'ident * 'lazy_term
  | AndElim of loc * 'term just * 'ident * 'term * 'ident * 'term
  | RewritingStep of
     loc * (string option * 'term) option * 'term  *
      [ `Term of 'term | `Auto of 'term auto_params
      | `Proof | `SolveWith of 'term ] *
      bool (* last step*)
  
type search_kind = [ `Locate | `Hint | `Match | `Elim ]

type print_kind = [ `Env | `Coer ]

type inline_param = IPPrefix of string         (* undocumented *)
		  | IPAs of Cic.object_flavour (* preferred flavour *)
		  | IPCoercions                (* show coercions *)
                  | IPDebug of int             (* set debug level *)
                  | IPProcedural               (* procedural rendering *)
                  | IPNoDefaults               (* no default-based tactics *)
		  | IPLevel of int             (* granularity level *)
                  | IPDepth of int             (* undocumented *)
                  | IPComments                 (* show statistics *)
                  | IPCR                       (* detect convertible rewriting *)

type ('term,'lazy_term) macro = 
  (* real macros *)
  | Eval of loc * 'lazy_term reduction * 'term
  | Check of loc * 'term 
  | Hint of loc * bool
  | AutoInteractive of loc * 'term auto_params
  | Inline of loc * string * inline_param list
     (* URI or base-uri, parameters *) 

type nmacro =
  | NCheck of loc * NotationPt.term
  | Screenshot of loc * string
  | NAutoInteractive of loc * NotationPt.term auto_params
  | NIntroGuess of loc

(** To be increased each time the command type below changes, used for "safe"
 * marshalling *)
let magic = 34

type ('term,'obj) command =
  | Index of loc * 'term option (* key *) * UriManager.uri (* value *)
  | Select of loc * UriManager.uri
  | Pump of loc * int
  | Coercion of loc * 'term * bool (* add_obj *) *
     int (* arity *) * int (* saturations *)
  | PreferCoercion of loc * 'term
  | Inverter of loc * string * 'term * bool list
  | Default of loc * string * UriManager.uri list
  | Drop of loc
  | Include of loc * bool (* normal? *) * [`New | `OldAndNew] * string 
  | Obj of loc * 'obj
  | Relation of
     loc * string * 'term * 'term * 'term option * 'term option * 'term option
  | Set of loc * string * string
  | Print of loc * string
  | Qed of loc

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

type punctuation_tactical =
  | Dot of loc
  | Semicolon of loc
  | Branch of loc
  | Shift of loc
  | Pos of loc * int list
  | Wildcard of loc
  | Merge of loc

type non_punctuation_tactical =
  | Focus of loc * int list
  | Unfocus of loc
  | Skip of loc

type ('term, 'lazy_term, 'reduction, 'obj, 'ident) code =
  | Command of loc * ('term, 'obj) command
  | NCommand of loc * ncommand
  | Macro of loc * ('term,'lazy_term) macro 
  | NMacro of loc * nmacro 
  | NTactic of loc * ntactic list
  | Tactic of loc * ('term, 'lazy_term, 'reduction, 'ident) tactic option
      * punctuation_tactical
  | NonPunctuationTactical of loc * non_punctuation_tactical
      * punctuation_tactical
             
type ('term, 'lazy_term, 'reduction, 'obj, 'ident) comment =
  | Note of loc * string
  | Code of loc * ('term, 'lazy_term, 'reduction, 'obj, 'ident) code
             
type ('term, 'lazy_term, 'reduction, 'obj, 'ident) statement =
  | Executable of loc * ('term, 'lazy_term, 'reduction, 'obj, 'ident) code
  | Comment of loc * ('term, 'lazy_term, 'reduction, 'obj, 'ident) comment
