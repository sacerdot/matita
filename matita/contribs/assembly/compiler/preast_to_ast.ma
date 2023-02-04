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

include "compiler/preast_tree.ma".
include "compiler/ast_tree.ma".
include "compiler/sigma.ma".

(* ************************* *)
(* PASSO 1 : da PREAST a AST *)
(* ************************* *)

(* NB: ASSERTO
   al parser spetta il compito di rigettare le condizioni statiche verificabili
    - divisione per valore 0
   al parser spetta il compito di collassare le espressioni statiche
    - val1+val2 -> val3, ...
   al parser spetta il compito di collassare gli statement con condizioni statiche
    - if(true) { b1 } else { b2 } -> b1, ...
   al parser spetta il compito di individuare divergenza e dead code
    - while(true) { b1 } -> loop infinito, ...
*)

(* operatore di cast *)
definition preast_to_ast_expr_check ≝
λd.λe:aux_env_type d.λsig:(Σt'.ast_expr d e t').λt:ast_type.
 match sig with [ sigma_intro t' expr ⇒
  match eq_ast_type t' t
   return λx.eq_ast_type t' t = x → option (ast_expr d e t)
  with
   [ true ⇒ λp:(eq_ast_type t' t = true).Some ? (eq_rect ? t' (λt.ast_expr d e t) expr t (eqasttype_to_eq ?? p))
   | false ⇒ λp:(eq_ast_type t' t = false).None ?
   ] (refl_eq ? (eq_ast_type t' t))
  ].

definition preast_to_ast_init_check ≝
λd.λe:aux_env_type d.λsig:Σt'.ast_init d e t'.λt:ast_type.
 match sig with [ sigma_intro t' expr ⇒
  match eq_ast_type t' t
   return λx.eq_ast_type t' t = x → option (ast_init d e t)
  with
   [ true ⇒ λp:(eq_ast_type t' t = true).Some ? (eq_rect ? t' (λt.ast_init d e t) expr t (eqasttype_to_eq ?? p))
   | false ⇒ λp:(eq_ast_type t' t = false).None ?
   ] (refl_eq ? (eq_ast_type t' t))
  ].

definition preast_to_ast_var_checkb ≝
λd.λe:aux_env_type d.λt:ast_type.λsig:(Σb'.ast_var d e b' t).λb:bool.
 match sig with [ sigma_intro b' var ⇒
  match eq_bool b' b
   return λx.eq_bool b' b = x → option (ast_var d e b t)
  with
   [ true ⇒ λp:(eq_bool b' b = true).Some ? (eq_rect ? b' (λb.ast_var d e b t) var b (eqbool_to_eq ?? p))
   | false ⇒ λp:(eq_bool b' b = false).None ?
   ] (refl_eq ? (eq_bool b' b))
  ].

definition preast_to_ast_var_checkt ≝
λd.λe:aux_env_type d.λb:bool.λsig:(Σt'.ast_var d e b t').λt:ast_type.
 match sig with [ sigma_intro t' var ⇒
  match eq_ast_type t' t
   return λx.eq_ast_type t' t = x → option (ast_var d e b t)
  with
   [ true ⇒ λp:(eq_ast_type t' t = true).Some ? (eq_rect ? t' (λt.ast_var d e b t) var t (eqasttype_to_eq ?? p))
   | false ⇒ λp:(eq_ast_type t' t = false).None ?
   ] (refl_eq ? (eq_ast_type t' t))
  ].

definition preast_to_ast_var_check ≝
λd.λe:aux_env_type d.λsig:(Σb'.(Σt'.ast_var d e b' t')).λb:bool.λt:ast_type.
 opt_map ?? (preast_to_ast_var_checkt d e (sigmaFst ?? sig) (sigmaSnd ?? sig) t)
  (λres1.opt_map ?? (preast_to_ast_var_checkb d e t ≪(sigmaFst ?? sig),res1≫ b)
   (λres2.Some ? res2)).

(*
 PREAST_EXPR_BYTE8 : byte8 → preast_expr
 PREAST_EXPR_WORD16: word16 → preast_expr
 PREAST_EXPR_WORD32: word32 → preast_expr
 PREAST_EXPR_NEG: preast_expr → preast_expr
 PREAST_EXPR_NOT: preast_expr → preast_expr
 PREAST_EXPR_COM: preast_expr → preast_expr
 PREAST_EXPR_ADD: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_SUB: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_MUL: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_DIV: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_SHR: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_SHL: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_AND: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_OR: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_XOR: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_GT : preast_expr → preast_expr → preast_expr
 PREAST_EXPR_GTE: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_LT : preast_expr → preast_expr → preast_expr
 PREAST_EXPR_LTE: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_EQ : preast_expr → preast_expr → preast_expr
 PREAST_EXPR_NEQ: preast_expr → preast_expr → preast_expr
 PREAST_EXPR_B8toW16 : preast_expr → preast_expr
 PREAST_EXPR_B8toW32 : preast_expr → preast_expr
 PREAST_EXPR_W16toB8 : preast_expr → preast_expr
 PREAST_EXPR_W16toW32: preast_expr → preast_expr
 PREAST_EXPR_W32toB8 : preast_expr → preast_expr
 PREAST_EXPR_W32toW16: preast_expr → preast_expr
 PREAST_EXPR_ID: preast_var → preast_expr
*)
let rec preast_to_ast_expr (preast:preast_expr) (d:nat) (e:aux_env_type d) on preast : option (Σt.ast_expr d e t) ≝
 match preast with
  [ PREAST_EXPR_BYTE8 val ⇒ Some ? ≪?,(AST_EXPR_BYTE8 d e val)≫
  | PREAST_EXPR_WORD16 val ⇒ Some ? ≪?,(AST_EXPR_WORD16 d e val)≫
  | PREAST_EXPR_WORD32 val ⇒ Some ? ≪?,(AST_EXPR_WORD32 d e val)≫

  | PREAST_EXPR_NEG subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).
     match (sigmaFst ?? sigmaRes) with
      [ AST_TYPE_BASE bType ⇒
       opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE bType))
        (λres.Some ? ≪?,(AST_EXPR_NEG d e ? res)≫)
      | _ ⇒ None ? ])
  | PREAST_EXPR_NOT subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).
     match (sigmaFst ?? sigmaRes) with
      [ AST_TYPE_BASE bType ⇒
       opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE bType))
        (λres.Some ? ≪?,(AST_EXPR_NOT d e ? res)≫)
      | _ ⇒ None ? ])
  | PREAST_EXPR_COM subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).
     match (sigmaFst ?? sigmaRes) with
      [ AST_TYPE_BASE bType ⇒
       opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE bType))
        (λres.Some ? ≪?,(AST_EXPR_COM d e ? res)≫)
      | _ ⇒ None ? ])

  | PREAST_EXPR_ADD subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_ADD d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_SUB subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_SUB d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_MUL subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_MUL d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_DIV subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_DIV d e ? res1 res2)≫))
       | _ ⇒ None ? ]))

  | PREAST_EXPR_SHR subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE AST_BASE_TYPE_BYTE8))
          (λres2.Some ? ≪?,(AST_EXPR_SHR d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_SHL subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE AST_BASE_TYPE_BYTE8))
          (λres2.Some ? ≪?,(AST_EXPR_SHL d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_AND subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_AND d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_OR subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_OR d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_XOR subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_XOR d e ? res1 res2)≫))
       | _ ⇒ None ? ]))

  | PREAST_EXPR_GT subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_GT d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_GTE subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_GTE d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_LT subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_LT d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_LTE subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_LTE d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_EQ subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_EQ d e ? res1 res2)≫))
       | _ ⇒ None ? ]))
  | PREAST_EXPR_NEQ subExpr1 subExpr2 ⇒
   opt_map ?? (preast_to_ast_expr subExpr1 d e)
    (λsigmaRes1:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr subExpr2 d e)
     (λsigmaRes2:(Σt.ast_expr d e t).
      match (sigmaFst ?? sigmaRes1) with
       [ AST_TYPE_BASE bType ⇒
        opt_map ?? (preast_to_ast_expr_check d e sigmaRes1 (AST_TYPE_BASE bType))
         (λres1.opt_map ?? (preast_to_ast_expr_check d e sigmaRes2 (AST_TYPE_BASE bType))
          (λres2.Some ? ≪?,(AST_EXPR_NEQ d e ? res1 res2)≫))
       | _ ⇒ None ? ]))

  | PREAST_EXPR_B8toW16 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_BYTE8))
     (λres.Some ? ≪?,(AST_EXPR_B8toW16 d e res)≫))
  | PREAST_EXPR_B8toW32 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_BYTE8))
     (λres.Some ? ≪?,(AST_EXPR_B8toW32 d e res)≫))
  | PREAST_EXPR_W16toB8 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_WORD16))
     (λres.Some ? ≪?,(AST_EXPR_W16toB8 d e res)≫))
  | PREAST_EXPR_W16toW32 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_WORD16))
     (λres.Some ? ≪?,(AST_EXPR_W16toW32 d e res)≫))
  | PREAST_EXPR_W32toB8 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_WORD32))
     (λres.Some ? ≪?,(AST_EXPR_W32toB8 d e res)≫))
  | PREAST_EXPR_W32toW16 subExpr ⇒
   opt_map ?? (preast_to_ast_expr subExpr d e)
    (λsigmaRes:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE AST_BASE_TYPE_WORD32))
     (λres.Some ? ≪?,(AST_EXPR_W32toW16 d e res)≫))

   | PREAST_EXPR_ID var ⇒
   opt_map ?? (preast_to_ast_var var d e)
    (λsigmaRes:(Σb.(Σt.ast_var d e b t)).
     match sigmaRes with [ sigma_intro b sigmaRes' ⇒
      match sigmaRes' with [ sigma_intro t _ ⇒
        opt_map ?? (preast_to_ast_var_check d e sigmaRes b t)
         (λres.Some ? ≪?,(AST_EXPR_ID d e ?? res)≫)]])
  ]
(*
 PREAST_VAR_ID: aux_str_type → preast_var
 PREAST_VAR_ARRAY: preast_var → preast_expr → preast_var
 PREAST_VAR_STRUCT: preast_var → nat → preast_var
*)
and preast_to_ast_var (preast:preast_var) (d:nat) (e:aux_env_type d) on preast : option (Σb.(Σt.ast_var d e b t)) ≝
 match preast with
  [ PREAST_VAR_ID name ⇒
   match checkb_desc_env d e name
    return λx.checkb_desc_env d e name = x → option (Σb.(Σt.ast_var d e b t))
   with
    [ true ⇒ λp:(checkb_desc_env d e name = true).
     let desc ≝ get_desc_env d e name in
     let b ≝ get_const_desc desc in
     let t ≝ get_type_desc desc in
     Some ? ≪b,≪t,(AST_VAR_ID d e b t (AST_ID d e name (checkbdescenv_to_checkdescenv d e name p)))≫≫     
    | false ⇒ λp:(checkb_desc_env d e name = false).None ?
    ] (refl_eq ? (checkb_desc_env d e name))

  | PREAST_VAR_ARRAY subVar expr ⇒
   opt_map ?? (preast_to_ast_var subVar d e)
    (λsigmaResV:(Σb.(Σt.ast_var d e b t)).
     match sigmaResV with [ sigma_intro b sigmaResV' ⇒
      match sigmaResV' with [ sigma_intro t _ ⇒
       match t with
        [ AST_TYPE_ARRAY subType dim ⇒
         opt_map ?? (preast_to_ast_var_check d e sigmaResV b (AST_TYPE_ARRAY subType dim))
          (λresVar.
           (* ASSERTO:
              1) se l'indice e' un'espressione riducibile ad un valore deve essere gia'
                 stato fatto dal parser, e qui controllo la condizione OUT_OF_BOUND
              2) se l'indice non e' un'espressione riducibile ad un valore il controllo
                 OUT_OF_BOUND sara' fatto a run time
           *)
           match (match expr with
                  [ PREAST_EXPR_BYTE8 val ⇒ (λx.leb (nat_of_byte8 val) dim)
                  | PREAST_EXPR_WORD16 val ⇒ (λx.leb (nat_of_word16 val) dim)
                  | PREAST_EXPR_WORD32 val ⇒ (λx.leb (nat_of_word32 val) dim)
                  | _ ⇒ (λx.true) ]) expr with
            [ true ⇒
             opt_map ?? (preast_to_ast_expr expr d e)
              (λsigmaResE:(Σt.ast_expr d e t).
               match sigmaFst ?? sigmaResE with
                [ AST_TYPE_BASE bType ⇒
                 opt_map ?? (preast_to_ast_expr_check d e sigmaResE (AST_TYPE_BASE bType))
                  (λresExpr.Some ? ≪b,≪subType,(AST_VAR_ARRAY d e b subType dim resVar (AST_BASE_EXPR d e bType resExpr))≫≫)
                | _ ⇒ None ? ])
            | false ⇒ None ? ])
        | _ ⇒ None ? ]]])

  | PREAST_VAR_STRUCT subVar field ⇒
   opt_map ?? (preast_to_ast_var subVar d e)
    (λsigmaRes:(Σb.(Σt.ast_var d e b t)).
     match sigmaRes with [ sigma_intro b sigmaRes' ⇒
      match sigmaRes' with [ sigma_intro t _ ⇒
       match t with
        [ AST_TYPE_STRUCT nelSubType ⇒
         opt_map ?? (preast_to_ast_var_check d e sigmaRes b (AST_TYPE_STRUCT nelSubType))
          (λresVar.
           match ltb field (len_neList ? nelSubType)
            return λx.(ltb field (len_neList ? nelSubType) = x) → option (Σb.(Σt.ast_var d e b t))
           with
            [ true ⇒ λp:(ltb field (len_neList ? nelSubType) = true).
             Some ? ≪b,≪(abs_nth_neList ? nelSubType field),(AST_VAR_STRUCT d e b nelSubType field resVar p)≫≫
            | false ⇒ λp:(ltb field (len_neList ? nelSubType) = false).None ?
            ] (refl_eq ? (ltb field (len_neList ? nelSubType)))
          )
        | _ ⇒ None ? ]]])
  ].

(*
 PREAST_INIT_VAL_BYTE8: byte8 → preast_init_val
 PREAST_INIT_VAL_WORD16: word16 → preast_init_val
 PREAST_INIT_VAL_WORD32: word32 → preast_init_val
 PREAST_INIT_VAL_ARRAY: ne_list preast_init_val → preast_init_val
 PREAST_INIT_VAL_STRUCT: ne_list preast_init_val → preast_init_val
*)
definition preast_to_ast_init_val_aux_array :
Πt.Πn.Prod (aux_ast_init_type t) (aux_ast_init_type (AST_TYPE_ARRAY t n)) → (aux_ast_init_type (AST_TYPE_ARRAY t (S n))) ≝
λt:ast_type.λn:nat.λx:Prod (aux_ast_init_type t) (aux_ast_init_type (AST_TYPE_ARRAY t n)).x.

definition preast_to_ast_init_val_aux_struct :
Πt.Πnel.Prod (aux_ast_init_type t) (aux_ast_init_type (AST_TYPE_STRUCT nel)) → (aux_ast_init_type (AST_TYPE_STRUCT («£t»&nel))) ≝
λt:ast_type.λnel:ne_list ast_type.λx:Prod (aux_ast_init_type t) (aux_ast_init_type (AST_TYPE_STRUCT nel)).x.

let rec preast_to_ast_init_val_aux (preast:preast_init_val) on preast : option (Σt.aux_ast_init_type t) ≝
 match preast with
  [ PREAST_INIT_VAL_BYTE8 val ⇒
   Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_BASE AST_BASE_TYPE_BYTE8),val≫
  | PREAST_INIT_VAL_WORD16 val ⇒
   Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_BASE AST_BASE_TYPE_WORD16),val≫
  | PREAST_INIT_VAL_WORD32 val ⇒
   Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_BASE AST_BASE_TYPE_WORD32),val≫

  | PREAST_INIT_VAL_ARRAY nelSubVal ⇒
   let rec aux (nel:ne_list preast_init_val) on nel : option (Σt.aux_ast_init_type t) ≝
    match nel with
     [ ne_nil h ⇒
      opt_map ?? (preast_to_ast_init_val_aux h)
       (λsigmaRes.match sigmaRes with [ sigma_intro t res ⇒
        Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_ARRAY t 0),res≫ ])
     | ne_cons h tl ⇒
      opt_map ?? (preast_to_ast_init_val_aux h)
       (λsigmaRes1:(Σt.aux_ast_init_type t).opt_map ?? (aux tl)
        (λsigmaRes2:(Σt.aux_ast_init_type t).
         match sigmaRes1 with [ sigma_intro t1 res1 ⇒
          match sigmaRes2 with [ sigma_intro t2 res2 ⇒
           match t2 with
            [ AST_TYPE_ARRAY bType dim ⇒
             match eq_ast_type t1 bType
              return λx.(eq_ast_type t1 bType = x) → option (Σt.aux_ast_init_type t)
             with
              [ true ⇒ λp:(eq_ast_type t1 bType = true).
               match eq_ast_type t2 (AST_TYPE_ARRAY bType dim)
                return λy.(eq_ast_type t2 (AST_TYPE_ARRAY bType dim) = y) → option (Σt.aux_ast_init_type t)
               with
                [ true ⇒ λp':(eq_ast_type t2 (AST_TYPE_ARRAY bType dim) = true).
                 Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_ARRAY bType (S dim)),
                                               (preast_to_ast_init_val_aux_array bType dim                                                               
                                                (pair (aux_ast_init_type bType) (aux_ast_init_type (AST_TYPE_ARRAY bType dim))
                                                      (eq_rect ? t1 (λw.aux_ast_init_type w) res1 bType (eqasttype_to_eq ?? p))
                                                         (eq_rect ? t2 (λz.aux_ast_init_type z) res2 (AST_TYPE_ARRAY bType dim) (eqasttype_to_eq ?? p'))))≫
                | false ⇒ λp':(eq_ast_type t2 (AST_TYPE_ARRAY bType dim) = false).None ?
                ] (refl_eq ? (eq_ast_type t2 (AST_TYPE_ARRAY bType dim)))
              | false ⇒ λp:(eq_ast_type t1 bType = false).None ?
              ] (refl_eq ? (eq_ast_type t1 bType))
            | _ ⇒ None ?
            ]]]))
     ] in aux nelSubVal

  | PREAST_INIT_VAL_STRUCT nelSubVal ⇒
   let rec aux (nel:ne_list preast_init_val) on nel : option (Σt.aux_ast_init_type t) ≝
    match nel with
     [ ne_nil h ⇒
      opt_map ?? (preast_to_ast_init_val_aux h)
       (λsigmaRes:(Σt.aux_ast_init_type t).match sigmaRes with [ sigma_intro t res ⇒
        Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_STRUCT («£t»)),res≫ ])
     | ne_cons h tl ⇒ 
      opt_map ?? (preast_to_ast_init_val_aux h)
       (λsigmaRes1:(Σt.aux_ast_init_type t).opt_map ?? (aux tl)
        (λsigmaRes2:(Σt.aux_ast_init_type t).
         match sigmaRes1 with [ sigma_intro t1 res1 ⇒
          match sigmaRes2 with [ sigma_intro t2 res2 ⇒
           match t2 with
            [ AST_TYPE_STRUCT nelSubType ⇒
             match eq_ast_type t2 (AST_TYPE_STRUCT nelSubType)
              return λx.(eq_ast_type t2 (AST_TYPE_STRUCT nelSubType) = x) → option (Σt.aux_ast_init_type t)
             with
              [ true ⇒ λp:(eq_ast_type t2 (AST_TYPE_STRUCT nelSubType) = true).
               Some (Σt.aux_ast_init_type t) ≪(AST_TYPE_STRUCT («£t1»&nelSubType)),
                                              (preast_to_ast_init_val_aux_struct ??
                                               (pair (aux_ast_init_type t1) (aux_ast_init_type (AST_TYPE_STRUCT nelSubType))
                                                     res1
                                                     (eq_rect ? t2 (λy.aux_ast_init_type y) res2 (AST_TYPE_STRUCT nelSubType) (eqasttype_to_eq ?? p))))≫
              | false ⇒ λp:(eq_ast_type t2 (AST_TYPE_STRUCT nelSubType) = false).None ?
              ] (refl_eq ? (eq_ast_type t2 (AST_TYPE_STRUCT nelSubType)))
            | _ ⇒ None ? ]]]))
     ] in aux nelSubVal
  ].

(*
 PREAST_INIT_VAR: preast_var → preast_init
 PREAST_INIT_VAL: preast_init_val → preast_init
*)
definition preast_to_ast_init : preast_init → Πd.Πe:aux_env_type d.option (Σt.ast_init d e t) ≝
λpreast:preast_init.λd.λe:aux_env_type d.match preast with
 [ PREAST_INIT_VAR var ⇒
  opt_map ?? (preast_to_ast_var var d e)
   (λsigmaRes:(Σb.(Σt.ast_var d e b t)).
    Some ? ≪?,(AST_INIT_VAR d e ?? (sigmaSnd ?? (sigmaSnd ?? sigmaRes)))≫)

 | PREAST_INIT_VAL val ⇒
  opt_map ?? (preast_to_ast_init_val_aux val)
   (λsigmaRes:(Σt.aux_ast_init_type t).
    Some ? ≪?,(AST_INIT_VAL d e ? (sigmaSnd ?? sigmaRes))≫)
 ].

(*
 PREAST_STM_ASG: preast_var → preast_expr → preast_stm
 PREAST_STM_WHILE: preast_expr → preast_decl → preast_stm
 PREAST_STM_IF: ne_list (Prod preast_expr preast_decl) → option preast_decl → preast_stm
*)
definition preast_to_ast_base_expr : preast_expr → Πd.Πe:aux_env_type d.option (ast_base_expr d e) ≝
λpreast:preast_expr.λd.λe:aux_env_type d.
 opt_map ?? (preast_to_ast_expr preast d e)
  (λsigmaRes:(Σt.ast_expr d e t).
   match sigmaFst ?? sigmaRes with
    [ AST_TYPE_BASE bType ⇒
     opt_map ?? (preast_to_ast_expr_check d e sigmaRes (AST_TYPE_BASE bType))
      (λres.Some ? (AST_BASE_EXPR d e ? res))
    | _ ⇒ None ? ]).

let rec preast_to_ast_stm (preast:preast_stm) (d:nat) (e:aux_env_type d) on preast : option (ast_stm d e) ≝
 match preast with
  [ PREAST_STM_ASG var expr ⇒
   opt_map ?? (preast_to_ast_var var d e)
    (λsigmaResV:(Σb.(Σt.ast_var d e b t)).
    match sigmaResV with [ sigma_intro _ sigmaResV' ⇒
     match sigmaResV' with [ sigma_intro t _ ⇒
      opt_map ?? (preast_to_ast_var_check d e sigmaResV false t)
       (λresVar.opt_map ?? (preast_to_ast_expr expr d e)
        (λsigmaResE:(Σt.ast_expr d e t).opt_map ?? (preast_to_ast_expr_check d e sigmaResE t)
         (λresExpr.Some ? (AST_STM_ASG d e t resVar resExpr)
         )))]])

  | PREAST_STM_WHILE expr decl ⇒
   opt_map ?? (preast_to_ast_base_expr expr d e)
    (λresExpr.opt_map ?? (preast_to_ast_decl decl (S d) (enter_env d e))
     (λresDecl.Some ? (AST_STM_WHILE d e resExpr resDecl)))

  | PREAST_STM_IF nelExprDecl optDecl ⇒
   opt_map ?? (fold_right_neList ?? (λh,t.opt_map ?? (preast_to_ast_base_expr (fst ?? h) d e)
                                     (λresExpr.opt_map ?? (preast_to_ast_decl (snd ?? h) (S d) (enter_env d e))
                                      (λresDecl.opt_map ?? t
                                       (λt'.Some ? («£(pair ?? resExpr resDecl)»&t')))))
                                    (Some ? (ne_nil ? (pair ?? (AST_BASE_EXPR d e AST_BASE_TYPE_BYTE8 (AST_EXPR_BYTE8 d e 〈x0,x0〉)) (AST_NO_DECL (S d) (enter_env d e) (nil ?)))))
                                    nelExprDecl)
    (λres.match optDecl with
     [ None ⇒ Some ? (AST_STM_IF d e (cut_last_neList ? res) (None ?))
     | Some decl ⇒ opt_map ?? (preast_to_ast_decl decl (S d) (enter_env d e))
      (λresDecl.Some ? (AST_STM_IF d e (cut_last_neList ? res) (Some ? resDecl)))
     ])
  ]
(* 
 PREAST_NO_DECL: list preast_stm → preast_decl
 PREAST_CONST_DECL: aux_str_type → ast_type → preast_init → preast_decl → preast_decl
 PREAST_VAR_DECL: aux_str_type → ast_type → option preast_init → preast_decl → preast_decl
*)
and preast_to_ast_decl (preast:preast_decl) (d:nat) (e:aux_env_type d) on preast : option (ast_decl d e) ≝
 match preast with
  [ PREAST_NO_DECL lPreastStm ⇒
    opt_map ?? (fold_right_list ?? (λh,t.opt_map ?? (preast_to_ast_stm h d e)
                                    (λh'.opt_map ?? t
                                     (λt'.Some ? ([h']@t')))) (Some ? (nil ?)) lPreastStm)  
     (λres.Some ? (AST_NO_DECL d e res))

  | PREAST_CONST_DECL decName decType initExpr subPreastDecl ⇒
   match checkb_not_already_def_env d e decName
    return λx.(checkb_not_already_def_env d e decName = x) → option (ast_decl d e)
   with
    [ true ⇒ λp:(checkb_not_already_def_env d e decName = true).
     opt_map ?? (preast_to_ast_decl subPreastDecl d (add_desc_env d e decName true decType))
      (λdecl.opt_map ?? (preast_to_ast_init initExpr d e)
       (λsigmaRes:(Σt:ast_type.ast_init d e t).opt_map ?? (preast_to_ast_init_check d e sigmaRes decType)
        (λresInit.Some ? (AST_CONST_DECL d e decName decType
                                         (checkbnotalreadydefenv_to_checknotalreadydefenv d e decName p) resInit decl))))
    | false ⇒ λp:(checkb_not_already_def_env d e decName = false).None ?
    ] (refl_eq ? (checkb_not_already_def_env d e decName))

  | PREAST_VAR_DECL decName decType optInitExpr subPreastDecl ⇒
   match checkb_not_already_def_env d e decName
    return λx.(checkb_not_already_def_env d e decName = x) → option (ast_decl d e)
   with
    [ true ⇒ λp:(checkb_not_already_def_env d e decName = true).
     opt_map ?? (preast_to_ast_decl subPreastDecl d (add_desc_env d e decName false decType))
      (λdecl.match optInitExpr with
       [ None ⇒ Some ? (AST_VAR_DECL d e decName decType
                                     (checkbnotalreadydefenv_to_checknotalreadydefenv d e decName p) (None ?) decl)
       | Some initExpr ⇒
        opt_map ?? (preast_to_ast_init initExpr d e)
         (λsigmaRes:(Σt:ast_type.ast_init d e t).opt_map ?? (preast_to_ast_init_check d e sigmaRes decType)
          (λresInit.Some ? (AST_VAR_DECL d e decName decType
                                         (checkbnotalreadydefenv_to_checknotalreadydefenv d e decName p) (Some ? resInit) decl)))])
    | false ⇒ λp:(checkb_not_already_def_env d e decName = false).None ?
    ] (refl_eq ? (checkb_not_already_def_env d e decName))
  ].

(*
 PREAST_ROOT: preast_decl → preast_root
*)
definition preast_to_ast ≝
λpreast:preast_root.match preast with
 [ PREAST_ROOT decl ⇒ opt_map ?? (preast_to_ast_decl decl O empty_env)
                       (λres.Some ? (AST_ROOT res)) ].
