(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: mlutil.mli 14786 2011-12-10 12:55:19Z letouzey $ i*)

open OcamlExtractionTable
open Miniml
open Coq

(*s Utility functions over ML types with meta. *)

val reset_meta_count : unit -> unit
val new_meta : 'a -> ml_type

val type_subst : int -> ml_type -> ml_type -> ml_type
val type_subst_list : ml_type list -> ml_type -> ml_type
val type_subst_vect : ml_type array -> ml_type -> ml_type

val instantiation : ml_schema -> ml_type

val needs_magic : ml_type * ml_type -> bool
val put_magic_if : bool -> ml_ast -> ml_ast
val put_magic : ml_type * ml_type -> ml_ast -> ml_ast

val generalizable : ml_ast -> bool

(*s ML type environment. *)

module Mlenv : sig
  type t
  val empty : t

  (* get the n-th more recently entered schema and instantiate it. *)
  val get : t -> int -> ml_type

  (* Adding a type in an environment, after generalizing free meta *)
  val push_gen : t -> ml_type -> t

  (* Adding a type with no [Tvar] *)
  val push_type : t -> ml_type -> t

  (* Adding a type with no [Tvar] nor [Tmeta] *)
  val push_std_type : t -> ml_type -> t
end

(*s Utility functions over ML types without meta *)

val type_mem_kn : NUri.uri -> ml_type -> bool

val type_maxvar : ml_type -> int

val type_decomp : ml_type -> ml_type list * ml_type
val type_recomp : ml_type list * ml_type -> ml_type

val var2var' : ml_type -> ml_type

type 'status abbrev_map =
 'status -> NReference.reference -> ('status * ml_type) option

val type_expand :
 (#status as 'status) -> 'status abbrev_map -> ml_type -> 'status * ml_type
val type_simpl : (#status as 'status) -> ml_type -> 'status * ml_type
val type_to_sign :
 (#status as 'status) -> 'status abbrev_map -> ml_type -> 'status * sign
val type_to_signature :
 (#status as 'status) -> 'status abbrev_map -> ml_type -> 'status * signature
val type_expunge :
 (#status as 'status) -> 'status abbrev_map -> ml_type -> 'status * ml_type
val type_expunge_from_sign :
 (#status as 'status) -> 'status abbrev_map -> signature -> ml_type -> 'status * ml_type

val isDummy : ml_type -> bool
val isKill : sign -> bool

val case_expunge : signature -> ml_ast -> ml_ident list * ml_ast
val term_expunge : signature -> ml_ident list * ml_ast -> ml_ast


(*s Special identifiers. [dummy_name] is to be used for dead code
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous_name : identifier
val dummy_name : identifier
val id_of_name : string -> identifier
val id_of_mlid : ml_ident -> identifier
val tmp_id : ml_ident -> ml_ident

(*s [collect_lambda MLlam(id1,...MLlam(idn,t)...)] returns
    the list [idn;...;id1] and the term [t]. *)

val collect_lams : ml_ast -> ml_ident list * ml_ast
val collect_n_lams : int -> ml_ast -> ml_ident list * ml_ast
val remove_n_lams : int -> ml_ast -> ml_ast
val nb_lams : ml_ast -> int
val named_lams : ml_ident list -> ml_ast -> ml_ast
val dummy_lams : ml_ast -> int -> ml_ast
val anonym_or_dummy_lams : ml_ast -> signature -> ml_ast

val eta_args_sign : int -> signature -> ml_ast list

(*s Utility functions over ML terms. *)

val mlapp : ml_ast -> ml_ast list -> ml_ast
val ast_map : (ml_ast -> ml_ast) -> ml_ast -> ml_ast
val ast_map_lift : (int -> ml_ast -> ml_ast) -> int -> ml_ast -> ml_ast
val ast_iter : (ml_ast -> unit) -> ml_ast -> unit
val ast_occurs : int -> ml_ast -> bool
val ast_occurs_itvl : int -> int -> ml_ast -> bool
val ast_lift : int -> ml_ast -> ml_ast
val ast_pop : ml_ast -> ml_ast
val ast_subst : ml_ast -> ml_ast -> ml_ast

val ast_glob_subst : ml_ast Refmap.t -> ml_ast -> ml_ast

val normalize : ml_ast -> ml_ast
val optimize_fix : ml_ast -> ml_ast
val inline : NReference.reference -> ml_ast -> bool

exception Impossible
val branch_as_fun : ml_type list -> ml_branch -> ml_ast
val branch_as_cst : ml_branch -> ml_ast

(* Classification of signatures *)

type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Keep] *)
  | UnsafeLogicalSig (* No [Keep], at least a [Kill Kother] *)
  | SafeLogicalSig (* only [Kill Ktype] *)

val sign_kind : signature -> sign_kind

val sign_no_final_keeps : signature -> signature
