(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id$ *)

(********************************* TERMS ************************************)

type univ_algebra = [ `Type | `Succ | `CProp ]

type universe = (univ_algebra * NUri.uri) list 
  (* Max of non-empty list of named universes, or their successor (when true) 
   * The empty list represents type0 *)

type sort = Prop | Type of universe

type implicit_annotation =
 [ `Closed | `Type | `Hole | `Tagged of string | `Term | `Typeof of int | `Vector ]


type lc_kind = Irl of int | Ctx of term list

and local_context = int * lc_kind             (* shift (0 -> no shift), 
                                                 subst (Irl n means id of
						 length n) *) 
and term =
 | Rel      of int                            (* DeBruijn index, 1 based    *)
 | Meta     of int * local_context
 | Appl     of term list                      (* arguments                  *)
 | Prod     of string * term * term           (* binder, source, target     *)
 | Lambda   of string * term * term           (* binder, source, target     *)
 | LetIn    of string * term * term * term    (* binder, type, term, body   *)
(* Cast \def degenerate LetIn *)
 | Const    of NReference.reference           (* ref has (indtype|constr)no *)
 | Sort     of sort                           (* sort                       *)
 | Implicit of implicit_annotation            (* ...                        *)
 | Match    of NReference.reference *         (* ind. reference,            *)
    term * term *                             (*  outtype, ind. term        *)
    term list                                 (*  patterns                  *)


(********************************* TYPING ***********************************)

type context_entry =                       (* A declaration or definition *)
 | Decl of term                            (* type *)
 | Def  of term * term                     (* body, type *)

type hypothesis = string * context_entry   (* name, entry *)

type context = hypothesis list

type meta_attr = 
  [ `Name of string 
  | `IsTerm | `IsType | `IsSort 
  | `InScope | `OutScope of int]

type meta_attrs = meta_attr list

type conjecture =  meta_attrs * context * term

type metasenv = (int * conjecture) list

type subst_entry = meta_attrs * context * term * term (* name,ctx,bo,ty *)

type substitution = (int * subst_entry) list


(******************************** OBJECTS **********************************)

type relevance = bool list (* relevance of arguments for conversion *)

                    (* relevance, name, recno, ty, bo *)
type inductiveFun = relevance * string * int * term * term 
  (* if coinductive, the int has no meaning and must be set to -1 *)

type constructor = relevance * string * term  (* id, type *)

type inductiveType = 
 relevance * string * term * constructor list    
 (* relevance, typename, arity, constructors *)

type def_flavour = (* presentational *)
  [ `Definition | `Fact | `Lemma | `Theorem | `Corollary | `Example ]

type def_pragma = (* pragmatic of the object *)
  [ `Coercion of int
  | `Elim of sort       (* elimination principle; universe is not relevant *)
  | `Projection         (* record projection *)
  | `InversionPrinciple (* inversion principle *)
  | `Variant 
  | `Local 
  | `Regular ]            (* Local = hidden technicality *)
 
type ind_pragma = (* pragmatic of the object *)
  [ `Record of (string * bool * int) list | `Regular ]
  (* inductive type that encodes a record; the arguments are the record 
   * fields names and if they are coercions and then the coercion arity *)

type generated = [ `Generated | `Provided ]

type c_attr = generated * def_flavour * def_pragma
type f_attr = generated * def_flavour * def_pragma
type i_attr = generated * ind_pragma

 (* invariant: metasenv and substitution have disjoint domains *)
type obj_kind =
 | Constant  of relevance * string * term option * term * c_attr
 | Fixpoint  of bool * inductiveFun list * f_attr
                (* true -> fix, funcs, arrts *)
 | Inductive of bool * int * inductiveType list * i_attr
                (* true -> inductive, leftno, types *)

 (* the int must be 0 if the object has no body *)
type obj = NUri.uri * int * metasenv * substitution * obj_kind
