(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "common/string.ma".
include "compiler/ast_type.ma".
include "num/word32.ma".

(* ****************** *)
(* PREALBERO DI TOKEN *)
(* ****************** *)

(* espressioni *)
ninductive preast_expr : Type ≝
  PREAST_EXPR_BYTE8 : byte8 → preast_expr
| PREAST_EXPR_WORD16: word16 → preast_expr
| PREAST_EXPR_WORD32: word32 → preast_expr

| PREAST_EXPR_NEG: preast_expr → preast_expr
| PREAST_EXPR_NOT: preast_expr → preast_expr
| PREAST_EXPR_COM: preast_expr → preast_expr

| PREAST_EXPR_ADD: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_SUB: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_MUL: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_DIV: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_SHR: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_SHL: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_AND: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_OR:  preast_expr → preast_expr → preast_expr
| PREAST_EXPR_XOR: preast_expr → preast_expr → preast_expr

| PREAST_EXPR_GT : preast_expr → preast_expr → preast_expr
| PREAST_EXPR_GTE: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_LT : preast_expr → preast_expr → preast_expr
| PREAST_EXPR_LTE: preast_expr → preast_expr → preast_expr
| PREAST_EXPR_EQ : preast_expr → preast_expr → preast_expr
| PREAST_EXPR_NEQ: preast_expr → preast_expr → preast_expr

| PREAST_EXPR_B8toW16 : preast_expr → preast_expr
| PREAST_EXPR_B8toW32 : preast_expr → preast_expr
| PREAST_EXPR_W16toB8 : preast_expr → preast_expr
| PREAST_EXPR_W16toW32: preast_expr → preast_expr
| PREAST_EXPR_W32toB8 : preast_expr → preast_expr
| PREAST_EXPR_W32toW16: preast_expr → preast_expr

| PREAST_EXPR_ID: preast_var → preast_expr

(* variabile: modificatori di array/struct dell'id *)
with preast_var : Type ≝
  PREAST_VAR_ID: aux_str_type → preast_var
| PREAST_VAR_ARRAY: preast_var → preast_expr → preast_var
| PREAST_VAR_STRUCT: preast_var → nat → preast_var.

(* -------------------------- *)

(* inizializzatori: ... valori ... *)
ninductive preast_init_val : Type ≝
  PREAST_INIT_VAL_BYTE8: byte8 → preast_init_val
| PREAST_INIT_VAL_WORD16: word16 → preast_init_val
| PREAST_INIT_VAL_WORD32: word32 → preast_init_val
| PREAST_INIT_VAL_ARRAY: ne_list preast_init_val → preast_init_val
| PREAST_INIT_VAL_STRUCT: ne_list preast_init_val → preast_init_val.

(*
 inizializzatori: ammesse solo due forme, no ibridi
  1) var1 = var2
  2) var = ... valori ...
*)
ninductive preast_init : Type ≝
  PREAST_INIT_VAR: preast_var → preast_init
| PREAST_INIT_VAL: preast_init_val → preast_init.

(* -------------------------- *)

(* statement: assegnamento/while/if else if else *)
ninductive preast_stm : Type ≝
  PREAST_STM_ASG: preast_var → preast_expr → preast_stm
| PREAST_STM_WHILE: preast_expr → preast_decl → preast_stm
| PREAST_STM_IF: ne_list (ProdT preast_expr preast_decl) → option preast_decl → preast_stm

(* dichiarazioni *)
with preast_decl : Type ≝
  PREAST_NO_DECL: list preast_stm → preast_decl
| PREAST_CONST_DECL: aux_str_type → ast_type → preast_init → preast_decl → preast_decl
| PREAST_VAR_DECL: aux_str_type → ast_type → option preast_init → preast_decl → preast_decl.

(* -------------------------- *)

(* programma *)
ninductive preast_root : Type ≝
  PREAST_ROOT: preast_decl → preast_root.

(* -------------------------- *)

(* programma vuoto *)
ndefinition empty_preast_prog ≝ PREAST_ROOT (PREAST_NO_DECL (nil ?)).
