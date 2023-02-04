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

include "compiler/environment.ma".

(* *************** *)
(* ALBERO DI TOKEN *)
(* *************** *)

(* id: accesso all'ambiente con stringa *)
inductive ast_id (d:nat) (e:aux_env_type d) : bool → ast_type → Type ≝
  AST_ID: ∀str:aux_str_type.
          (* D *) (check_desc_env d e str) → (ast_id d e (get_const_desc (get_desc_env d e str)) (get_type_desc (get_desc_env d e str))).

(* -------------------------- *)

(* espressioni *)
inductive ast_expr (d:nat) (e:aux_env_type d) : ast_type → Type ≝
  AST_EXPR_BYTE8 : byte8 → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_WORD16: word16 → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
| AST_EXPR_WORD32: word32 → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)

| AST_EXPR_NEG: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_NOT: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_COM: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)

| AST_EXPR_ADD: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_SUB: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_MUL: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_DIV: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_SHR: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_SHL: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_AND: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_OR:  ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)
| AST_EXPR_XOR: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t)

| AST_EXPR_GT : ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_GTE: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_LT : ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_LTE: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_EQ : ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_NEQ: ∀t:ast_base_type.
                ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE t) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)

| AST_EXPR_B8toW16 : ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
| AST_EXPR_B8toW32 : ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
| AST_EXPR_W16toB8 : ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_W16toW32: ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
| AST_EXPR_W32toB8 : ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
| AST_EXPR_W32toW16: ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) → ast_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16)

| AST_EXPR_ID: ∀b:bool.∀t:ast_type.
               ast_var d e b t → ast_expr d e t

(* variabile: modificatori di array/struct dell'id *)
with ast_var : bool → ast_type → Type ≝
  AST_VAR_ID: ∀b:bool.∀t:ast_type.
              ast_id d e b t → ast_var d e b t
| AST_VAR_ARRAY: ∀b:bool.∀t:ast_type.∀n:nat.
                 ast_var d e b (AST_TYPE_ARRAY t n) → ast_base_expr d e → ast_var d e b t
| AST_VAR_STRUCT: ∀b:bool.∀nel:ne_list ast_type.∀n:nat.
                  ast_var d e b (AST_TYPE_STRUCT nel) → (* D *) (ltb n (len_neList ? nel) = true) → ast_var d e b (abs_nth_neList ? nel n)

(* espressioni generalizzate: anche non uniformi per tipo *)
with ast_base_expr : Type ≝
  AST_BASE_EXPR: ∀t:ast_base_type.
                 ast_expr d e (AST_TYPE_BASE t) → ast_base_expr d e.

(* -------------------------- *)

let rec aux_ast_init_type (t:ast_type) on t : Type ≝
 match t with
  [ AST_TYPE_BASE bType ⇒ match bType with
   [ AST_BASE_TYPE_BYTE8 ⇒ byte8
   | AST_BASE_TYPE_WORD16 ⇒ word16
   | AST_BASE_TYPE_WORD32 ⇒ word32
   ] 
  | AST_TYPE_ARRAY subType dim ⇒
   let T ≝ aux_ast_init_type subType in
   let rec aux (n:nat) on n ≝
    match n with
     [ O ⇒ T
     | S n' ⇒ Prod T (aux n')
     ] in
   aux dim 
  | AST_TYPE_STRUCT nelSubType ⇒
   let rec aux (nel:ne_list ast_type) on nel ≝
    match nel with
     [ ne_nil h ⇒ aux_ast_init_type h
     | ne_cons h t ⇒ Prod (aux_ast_init_type h) (aux t)
     ] in
    aux nelSubType 
  ].

(*
 inizializzatori: ammesse solo due forme, no ibridi
  1) var1 = var2
  2) var = ... valori ...
*) 
inductive ast_init (d:nat) (e:aux_env_type d) : ast_type → Type ≝
  AST_INIT_VAR: ∀b:bool.∀t:ast_type.
                ast_var d e b t → ast_init d e t
| AST_INIT_VAL: ∀t:ast_type.
                aux_ast_init_type t → ast_init d e t.

(* -------------------------- *)

(* statement: assegnamento/while/if else if else *)
inductive ast_stm : Πd:nat.aux_env_type d → Type ≝
  AST_STM_ASG: ∀d.∀e:aux_env_type d.∀t:ast_type.
               ast_var d e false t → ast_expr d e t → ast_stm d e
| AST_STM_WHILE: ∀d.∀e:aux_env_type d.
                 ast_base_expr d e → ast_decl (S d) (enter_env d e) → ast_stm d e
| AST_STM_IF: ∀d.∀e:aux_env_type d.
              ne_list (Prod (ast_base_expr d e) (ast_decl (S d) (enter_env d e))) → option (ast_decl (S d) (enter_env d e)) → ast_stm d e

(* dichiarazioni *)
with ast_decl : Πd:nat.aux_env_type d → Type ≝
  AST_NO_DECL: ∀d.∀e:aux_env_type d.
               list (ast_stm d e) → ast_decl d e
| AST_CONST_DECL: ∀d.∀e:aux_env_type d.∀str:aux_str_type.∀t:ast_type.
                  (* D *) (check_not_already_def_env d e str) → ast_init d e t → ast_decl d (add_desc_env d e str true t) → ast_decl d e
| AST_VAR_DECL: ∀d.∀e:aux_env_type d.∀str:aux_str_type.∀t:ast_type.
                (* D *) (check_not_already_def_env d e str) → option (ast_init d e t) → ast_decl d (add_desc_env d e str false t) → ast_decl d e.

(* -------------------------- *)

(* programma *)
inductive ast_root : Type ≝
  AST_ROOT: ast_decl O empty_env → ast_root.

(* -------------------------- *)

(* programma vuoto *)
definition empty_ast_prog ≝ AST_ROOT (AST_NO_DECL O empty_env (nil ?)).
