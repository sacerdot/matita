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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "compiler/env_to_flatenv.ma".

(* **************************** *)
(* ALBERO DI TOKEN CON FLAT ENV *)
(* **************************** *)

(* id: accesso all'ambiente con stringa *)
inductive astfe_id (e:aux_flatEnv_type) : bool → ast_type → Type ≝
  ASTFE_ID: ∀str:aux_strId_type.
            (* D *) check_desc_flatEnv e str → astfe_id e (get_const_desc (get_desc_flatEnv e str)) (get_type_desc (get_desc_flatEnv e str)).

(* -------------------------- *)

(* espressioni *)
inductive astfe_expr (e:aux_flatEnv_type) : ast_type → Type ≝
  ASTFE_EXPR_BYTE8 : byte8 → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_WORD16: word16 → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
| ASTFE_EXPR_WORD32: word32 → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)

| ASTFE_EXPR_NEG: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_NOT: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_COM: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)

| ASTFE_EXPR_ADD: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_SUB: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_MUL: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_DIV: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_SHR: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_SHL: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_AND: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_OR:  ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)
| ASTFE_EXPR_XOR: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t)

| ASTFE_EXPR_GT : ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_GTE: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_LT : ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_LTE: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_EQ : ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_NEQ: ∀t:ast_base_type.
                  astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE t) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)

| ASTFE_EXPR_B8toW16 : astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
| ASTFE_EXPR_B8toW32 : astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
| ASTFE_EXPR_W16toB8 : astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_W16toW32: astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
| ASTFE_EXPR_W32toB8 : astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| ASTFE_EXPR_W32toW16: astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) → astfe_expr e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)

| ASTFE_EXPR_ID: ∀b:bool.∀t:ast_type.
                 astfe_var e b t → astfe_expr e t

(* variabile: modificatori di array/struct dell'id *)
with astfe_var : bool → ast_type → Type ≝
  ASTFE_VAR_ID: ∀b:bool.∀t:ast_type.
                astfe_id e b t → astfe_var e b t
| ASTFE_VAR_ARRAY: ∀b:bool.∀t:ast_type.∀n:nat.
                   astfe_var e b (AST_TYPE_ARRAY t n) → astfe_base_expr e → astfe_var e b t
| ASTFE_VAR_STRUCT: ∀b:bool.∀nel:ne_list ast_type.∀n:nat.
                    astfe_var e b (AST_TYPE_STRUCT nel) → astfe_var e b (abs_nth_neList ? nel n)

(* espressioni generalizzate: anche non uniformi per tipo *)
with astfe_base_expr : Type ≝
  ASTFE_BASE_EXPR: ∀t:ast_base_type.
                   astfe_expr e (AST_TYPE_BASE t) → astfe_base_expr e.

(* -------------------------- *)

(*
 inizializzatori: ammesse solo due forme, no ibridi
  1) var1 = var2
  2) var = ... valori ...
*) 
inductive astfe_init (e:aux_flatEnv_type) : ast_type → Type ≝
  ASTFE_INIT_VAR: ∀b:bool.∀t:ast_type.
                  astfe_var e b t → astfe_init e t
| ASTFE_INIT_VAL: ∀t:ast_type.
                  aux_ast_init_type t → astfe_init e t.

(* -------------------------- *)

(* statement: assegnamento/while/if else if else + conversione di dichiarazione *)
inductive astfe_stm (e:aux_flatEnv_type) : Type ≝
  ASTFE_STM_ASG: ∀t:ast_type.
                 astfe_var e false t → astfe_expr e t → astfe_stm e
| ASTFE_STM_INIT: ∀b:bool.∀t:ast_type.
                  astfe_id e b t → astfe_init e t → astfe_stm e
| ASTFE_STM_WHILE: astfe_base_expr e → astfe_body e → astfe_stm e
| ASTFE_STM_IF: ne_list (Prod (astfe_base_expr e) (astfe_body e)) → option (astfe_body e) → astfe_stm e

(* dichiarazioni *)
with astfe_body : Type ≝
  ASTFE_BODY: list (astfe_stm e) → astfe_body e.

(* -------------------------- *)

(* programma *)
inductive astfe_root (e:aux_flatEnv_type) : Type ≝
  ASTFE_ROOT: astfe_body e → astfe_root e.

(* -------------------------- *)

(* programma vuoto *)
definition empty_astfe_prog ≝ ASTFE_ROOT empty_flatEnv (ASTFE_BODY empty_flatEnv (nil ?)).
