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

(*****************************************************************************)
(*                                                                           *)
(*                               PROJECT HELM                                *)
(*                                                                           *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>              *)
(*                                 29/11/2000                                *)
(*                                                                           *)
(* This module defines the internal representation of the objects (variables,*)
(* blocks of (co)inductive definitions and constants) and the terms of cic   *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

(* STUFF TO MANAGE IDENTIFIERS *)
type id = string  (* the abstract type of the (annotated) node identifiers *)
type 'term explicit_named_substitution = (UriManager.uri * 'term) list

type implicit_annotation = [ `Closed | `Type | `Hole ]

(* INTERNAL REPRESENTATION OF CIC OBJECTS AND TERMS *)

type sort =
   Prop
 | Set
 | Type of CicUniv.universe
 | CProp of CicUniv.universe

type name =
 | Name of string
 | Anonymous

type object_flavour =
  [ `Definition
  | `MutualDefinition
  | `Fact
  | `Lemma
  | `Remark
  | `Theorem
  | `Variant
  | `Axiom
  ]

type object_class =
  [ `Elim of sort   (** elimination principle; if sort is Type, the universe is
                      * not relevant *)
  | `Record of (string * bool * int) list (** 
                        inductive type that encodes a record; the arguments are
                        the record fields names and if they are coercions and
                        then the coercion arity *)
  | `Projection     (** record projection *)
  | `InversionPrinciple (** inversion principle *)
  ]

type attribute =
  [ `Class of object_class
  | `Flavour of object_flavour 
  | `Generated
  ]

type term =
   Rel of int                                       (* DeBrujin index, 1 based*)
 | Var of UriManager.uri *                          (* uri,                   *)
     term explicit_named_substitution               (*  explicit named subst. *)
 | Meta of int * (term option) list                 (* numeric id,    *)
                                                    (*  local context *)
 | Sort of sort                                     (* sort *)
 | Implicit of implicit_annotation option           (* *)
 | Cast of term * term                              (* value, type *)
 | Prod of name * term * term                       (* binder, source, target *)
 | Lambda of name * term * term                     (* binder, source, target *)
 | LetIn of name * term * term * term               (* binder, term, type, target *)
 | Appl of term list                                (* arguments *)
 | Const of UriManager.uri *                        (* uri,                   *)
     term explicit_named_substitution               (*  explicit named subst. *)
 | MutInd of UriManager.uri * int *                 (* uri, typeno, *)
     term explicit_named_substitution               (*  explicit named subst. *)
                                                    (* typeno is 0 based      *)
 | MutConstruct of UriManager.uri *                 (* uri,                   *)
    int * int *                                     (*  typeno, consno        *)
     term explicit_named_substitution               (*  explicit named subst. *)
                                                    (* typeno is 0 based      *)
                                                    (* consno is 1 based      *)
 | MutCase of UriManager.uri *                      (* ind. uri,             *)
    int *                                           (*  ind. typeno,         *)
    term * term *                                   (*  outtype, ind. term   *)
    term list                                       (*  patterns             *)
 | Fix of int * inductiveFun list                   (* funno (0 based), funs *)
 | CoFix of int * coInductiveFun list               (* funno (0 based), funs *)
and obj =
   Constant of string * term option * term *      (* id, body, type,          *)
    UriManager.uri list * attribute list          (*  parameters              *)
 | Variable of string * term option * term *      (* name, body, type         *)
    UriManager.uri list * attribute list          (* parameters               *)
 | CurrentProof of string * metasenv * term *     (* name, conjectures, body, *)
    term * UriManager.uri list * attribute list   (*  type, parameters        *)
 | InductiveDefinition of inductiveType list *    (* inductive types,         *)
    UriManager.uri list * int * attribute list    (*  params, left params no  *)
and inductiveType = 
 string * bool * term *                       (* typename, inductive, arity *)
  constructor list                            (*  constructors              *)
and constructor =
 string * term                                (* id, type *)
and inductiveFun =
 string * int * term * term                   (* name, ind. index, type, body *)
and coInductiveFun =
 string * term * term                         (* name, type, body *)

(* a metasenv is a list of declarations of metas in declarations *)
(* order (i.e. [oldest ; ... ; newest]). Older variables can not *)
(* depend on new ones.                                           *)
and conjecture = int * context * term
and metasenv = conjecture list
and substitution = (int * (context * term * term)) list



(* a metasenv is a list of declarations of metas in declarations *)
(* order (i.e. [oldest ; ... ; newest]). Older variables can not *)
(* depend on new ones.                                           *)
and annconjecture = id * int * anncontext * annterm
and annmetasenv = annconjecture list

and annterm =
   ARel of id * id * int *                          (* idref, DeBrujin index, *)
    string                                          (*  binder                *)
 | AVar of id * UriManager.uri *                    (* uri,                   *)
    annterm explicit_named_substitution             (*  explicit named subst. *)
 | AMeta of id * int * (annterm option) list        (* numeric id,    *)
                                                    (*  local context *)
 | ASort of id * sort                               (* sort *)
 | AImplicit of id * implicit_annotation option     (* *)
 | ACast of id * annterm * annterm                  (* value, type *)
 | AProd of id * name * annterm * annterm           (* binder, source, target *)
 | ALambda of id * name * annterm * annterm         (* binder, source, target *)
 | ALetIn of id * name * annterm * annterm *  annterm (* binder, term, type, target *)
 | AAppl of id * annterm list                       (* arguments *)
 | AConst of id * UriManager.uri *                  (* uri,                   *)
    annterm explicit_named_substitution             (*  explicit named subst. *)
 | AMutInd of id * UriManager.uri * int *           (* uri, typeno            *)
    annterm explicit_named_substitution             (*  explicit named subst. *)
                                                    (* typeno is 0 based *)
 | AMutConstruct of id * UriManager.uri *           (* uri,                   *)
    int * int *                                     (*  typeno, consno        *)
    annterm explicit_named_substitution             (*  explicit named subst. *)
                                                    (* typeno is 0 based *)
                                                    (* consno is 1 based *)
 | AMutCase of id * UriManager.uri *                (* ind. uri,             *)
    int *                                           (*  ind. typeno,         *)
    annterm * annterm *                             (*  outtype, ind. term   *)
    annterm list                                    (*  patterns             *)
 | AFix of id * int * anninductiveFun list          (* funno, functions *)
 | ACoFix of id * int * anncoInductiveFun list      (* funno, functions *)
and annobj =
   AConstant of id * id option * string *           (* name,         *)
    annterm option * annterm *                      (*  body, type,  *)
    UriManager.uri list * attribute list            (*  parameters   *)
 | AVariable of id *
    string * annterm option * annterm *             (* name, body, type *)
    UriManager.uri list * attribute list            (*  parameters      *)
 | ACurrentProof of id * id *
    string * annmetasenv *                          (*  name, conjectures,    *)
    annterm * annterm * UriManager.uri list *       (*  body,type,parameters  *)
    attribute list
 | AInductiveDefinition of id *
    anninductiveType list *                         (* inductive types ,      *)
    UriManager.uri list * int * attribute list      (*  parameters,n ind. pars*)
and anninductiveType = 
 id * string * bool * annterm *               (* typename, inductive, arity *)
  annconstructor list                         (*  constructors              *)
and annconstructor =
 string * annterm                             (* id, type *)
and anninductiveFun =
 id * string * int * annterm * annterm        (* name, ind. index, type, body *)
and anncoInductiveFun =
 id * string * annterm * annterm              (* name, type, body *)
and annotation =
 string

and context_entry =                            (* A declaration or definition *)
   Decl of term
 | Def of term * term                          (* body, type *)

and hypothesis =
 (name * context_entry) option               (* None means no more accessible *)

and context = hypothesis list

and anncontext_entry =                         (* A declaration or definition *)
   ADecl of annterm
 | ADef of annterm * annterm

and annhypothesis =
 id * (name * anncontext_entry) option       (* None means no more accessible *)

and anncontext = annhypothesis list
;;

type lazy_term =
 context -> metasenv -> CicUniv.universe_graph ->
  term * metasenv * CicUniv.universe_graph

type anntarget =
   Object of annobj         (* if annobj is a Constant, this is its type *)
 | ConstantBody of annobj
 | Term of annterm
 | Conjecture of annconjecture
 | Hypothesis of annhypothesis

module CicHash =
 Hashtbl.Make
  (struct
    type t = term
    let equal = (==)
    let hash = Hashtbl.hash_param 100 1000 
   end)
;;

