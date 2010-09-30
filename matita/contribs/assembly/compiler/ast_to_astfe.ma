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

include "compiler/astfe_tree.ma".
include "compiler/sigma.ma".

(* ************************ *)
(* PASSO 2 : da AST a ASTFE *)
(* ************************ *)

(*
  AST_ID: ∀str:aux_str_type.
          (check_desc_env d e str) → (ast_id d e (get_const_desc (get_desc_env d e str)) (get_type_desc (get_desc_env d e str)))
*)
lemma ast_to_astfe_id :
 ∀d.∀e:aux_env_type d.∀b,t.∀ast:ast_id d e b t.
 ∀m:aux_map_type d.∀fe.
 ∀dimInv:env_to_flatEnv_inv d e m fe.
 astfe_id fe b t.
 intros 7;
 elim a 0;
 intros 3;
 lapply (ASTFE_ID fe (STR_ID a1 (get_id_map d m a1)) ?);
 [ apply (proj2 ?? (proj1 ?? ((env_to_flatEnv_inv_last ???? H1) a1 H)))
 | rewrite > (proj2 ?? ((env_to_flatEnv_inv_last ???? H1) a1 H));
   apply Hletin
 ].
qed.

lemma ast_to_astfe_retype_id :
 ∀fe,b,t.∀ast:astfe_id fe b t.
 ∀d.∀e:aux_env_type d.∀m:aux_map_type d.∀fe'.
 ∀dimInv:env_to_flatEnv_inv d e m fe'.
 ∀dimLe:le_flatEnv fe fe' = true.
 astfe_id fe' b t.
 intros 8;
 elim a 0;
 intros 4;
 lapply (ASTFE_ID fe' a1 ?);
 [ apply (leflatenv_to_check fe fe' a1 H2 H)
 | rewrite > (leflatenv_to_get fe fe' a1 H2 H);
   apply Hletin
 ].
qed.

(*
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
*)
let rec ast_to_astfe_expr d (e:aux_env_type d) t (ast:ast_expr d e t)
                          (m:aux_map_type d) fe (dimInv:env_to_flatEnv_inv d e m fe) on ast : astfe_expr fe t ≝
 match ast
  return λW.λa:ast_expr d e W.astfe_expr fe W
 with
  [ AST_EXPR_BYTE8 val ⇒
   ASTFE_EXPR_BYTE8 fe val
  | AST_EXPR_WORD16 val ⇒
   ASTFE_EXPR_WORD16 fe val
  | AST_EXPR_WORD32 val ⇒
   ASTFE_EXPR_WORD32 fe val

  | AST_EXPR_NEG bType sExpr ⇒
   ASTFE_EXPR_NEG fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr m fe dimInv)
  | AST_EXPR_NOT bType sExpr ⇒
   ASTFE_EXPR_NOT fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr m fe dimInv)
  | AST_EXPR_COM bType sExpr ⇒
   ASTFE_EXPR_COM fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr m fe dimInv)

  | AST_EXPR_ADD bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_ADD fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_SUB bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SUB fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_MUL bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_MUL fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_DIV bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_DIV fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_SHR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SHR fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr2 m fe dimInv)
  | AST_EXPR_SHL bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SHL fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr2 m fe dimInv)
  | AST_EXPR_AND bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_AND fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_OR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_OR fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_XOR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_XOR fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)

  | AST_EXPR_GT bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_GT fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                          (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_GTE bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_GTE fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_LT bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_LT fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                          (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_LTE bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_LTE fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_EQ bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_EQ fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                          (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)
  | AST_EXPR_NEQ bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_NEQ fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr1 m fe dimInv)
                           (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr2 m fe dimInv)

  | AST_EXPR_B8toW16 sExpr ⇒
   ASTFE_EXPR_B8toW16 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr m fe dimInv)
  | AST_EXPR_B8toW32 sExpr ⇒
   ASTFE_EXPR_B8toW32 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr m fe dimInv)
  | AST_EXPR_W16toB8 sExpr ⇒
   ASTFE_EXPR_W16toB8 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) sExpr m fe dimInv)
  | AST_EXPR_W16toW32 sExpr ⇒
   ASTFE_EXPR_W16toW32 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD16) sExpr m fe dimInv)
  | AST_EXPR_W32toB8 sExpr ⇒
   ASTFE_EXPR_W32toB8 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) sExpr m fe dimInv)
  | AST_EXPR_W32toW16 sExpr ⇒
   ASTFE_EXPR_W32toW16 fe (ast_to_astfe_expr d e (AST_TYPE_BASE AST_BASE_TYPE_WORD32) sExpr m fe dimInv)

  | AST_EXPR_ID b sType var ⇒
   ASTFE_EXPR_ID fe b sType (ast_to_astfe_var d e b sType var m fe dimInv)

  ]
(*
  AST_VAR_ID: ∀b:bool.∀t:ast_type.
              ast_id d e b t → ast_var d e b t
| AST_VAR_ARRAY: ∀b:bool.∀t:ast_type.∀n:nat.
                 ast_var d e b (AST_TYPE_ARRAY t n) → ast_base_expr d e → ast_var d e b t
| AST_VAR_STRUCT: ∀b:bool.∀nel:ne_list ast_type.∀n:nat.
                  ast_var d e b (AST_TYPE_STRUCT nel) → (ltb n (len_neList ? nel) = true) → ast_var d e b (abs_nth_neList ? nel n)
*)
and ast_to_astfe_var d (e:aux_env_type d) b t (ast:ast_var d e b t)
                     (m:aux_map_type d) fe (dimInv:env_to_flatEnv_inv d e m fe) on ast : astfe_var fe b t ≝
 match ast
  return λW,X.λa:ast_var d e W X.astfe_var fe W X
 with
  [ AST_VAR_ID sB sType sId ⇒
   ASTFE_VAR_ID fe sB sType (ast_to_astfe_id d e sB sType sId m fe dimInv)

  | AST_VAR_ARRAY sB sType sDim sVar sExpr ⇒
   ASTFE_VAR_ARRAY fe sB sType sDim (ast_to_astfe_var d e sB (AST_TYPE_ARRAY sType sDim) sVar m fe dimInv)
                                    (ast_to_astfe_base_expr d e sExpr m fe dimInv)

  | AST_VAR_STRUCT sB sType sField sVar sLtb ⇒
   ASTFE_VAR_STRUCT fe sB sType sField (ast_to_astfe_var d e sB (AST_TYPE_STRUCT sType) sVar m fe dimInv)                                                                                    
  ]
(*
  AST_BASE_EXPR: ∀t:ast_base_type.
                 ast_expr d e (AST_TYPE_BASE t) → ast_base_expr d e

*)
and ast_to_astfe_base_expr d (e:aux_env_type d) (ast:ast_base_expr d e)
                           (m:aux_map_type d) fe (dimInv:env_to_flatEnv_inv d e m fe) on ast : astfe_base_expr fe ≝
 match ast
  return λa:ast_base_expr d e.astfe_base_expr fe
 with
  [ AST_BASE_EXPR bType sExpr ⇒
   ASTFE_BASE_EXPR fe bType (ast_to_astfe_expr d e (AST_TYPE_BASE bType) sExpr m fe dimInv)
  ].

let rec ast_to_astfe_retype_expr fe t (ast:astfe_expr fe t)
                                 d (e:aux_env_type d) (m:aux_map_type d) fe'
                                 (dimInv:env_to_flatEnv_inv d e m fe') (dimLe:le_flatEnv fe fe' = true) on ast : astfe_expr fe' t ≝
 match ast
  return λW.λa:astfe_expr fe W.astfe_expr fe' W
 with
  [ ASTFE_EXPR_BYTE8 val ⇒
   ASTFE_EXPR_BYTE8 fe' val
  | ASTFE_EXPR_WORD16 val ⇒
   ASTFE_EXPR_WORD16 fe' val
  | ASTFE_EXPR_WORD32 val ⇒
   ASTFE_EXPR_WORD32 fe' val

  | ASTFE_EXPR_NEG bType sExpr ⇒
   ASTFE_EXPR_NEG fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_NOT bType sExpr ⇒
   ASTFE_EXPR_NOT fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_COM bType sExpr ⇒
   ASTFE_EXPR_COM fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr d e m fe' dimInv dimLe)

  | ASTFE_EXPR_ADD bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_ADD fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_SUB bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SUB fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_MUL bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_MUL fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_DIV bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_DIV fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_SHR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SHR fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_SHL bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_SHL fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_AND bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_AND fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_OR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_OR fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_XOR bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_XOR fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)

  | ASTFE_EXPR_GT bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_GT fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                           (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_GTE bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_GTE fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_LT bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_LT fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                           (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_LTE bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_LTE fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_EQ bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_EQ fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                           (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)
  | ASTFE_EXPR_NEQ bType sExpr1 sExpr2 ⇒
   ASTFE_EXPR_NEQ fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr1 d e m fe' dimInv dimLe)
                            (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr2 d e m fe' dimInv dimLe)

  | ASTFE_EXPR_B8toW16 sExpr ⇒
   ASTFE_EXPR_B8toW16 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_B8toW32 sExpr ⇒
   ASTFE_EXPR_B8toW32 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_W16toB8 sExpr ⇒
   ASTFE_EXPR_W16toB8 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_WORD16) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_W16toW32 sExpr ⇒
   ASTFE_EXPR_W16toW32 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_WORD16) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_W32toB8 sExpr ⇒
   ASTFE_EXPR_W32toB8 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_WORD32) sExpr d e m fe' dimInv dimLe)
  | ASTFE_EXPR_W32toW16 sExpr ⇒
   ASTFE_EXPR_W32toW16 fe' (ast_to_astfe_retype_expr fe (AST_TYPE_BASE AST_BASE_TYPE_WORD32) sExpr d e m fe' dimInv dimLe)

  | ASTFE_EXPR_ID b sType var ⇒
   ASTFE_EXPR_ID fe' b sType (ast_to_astfe_retype_var fe b sType var d e m fe' dimInv dimLe)

  ]
and ast_to_astfe_retype_var fe b t (ast:astfe_var fe b t)
                            d (e:aux_env_type d) (m:aux_map_type d) fe'
                            (dimInv:env_to_flatEnv_inv d e m fe') (dimLe:le_flatEnv fe fe' = true) on ast : astfe_var fe' b t ≝
 match ast
  return λW,X.λa:astfe_var fe W X.astfe_var fe' W X
 with
  [ ASTFE_VAR_ID sB sType sId ⇒
   ASTFE_VAR_ID fe' sB sType (ast_to_astfe_retype_id fe sB sType sId d e m fe' dimInv dimLe)

  | ASTFE_VAR_ARRAY sB sType sDim sVar sExpr ⇒
   ASTFE_VAR_ARRAY fe' sB sType sDim (ast_to_astfe_retype_var fe sB (AST_TYPE_ARRAY sType sDim) sVar d e m fe' dimInv dimLe)
                                     (ast_to_astfe_retype_base_expr fe sExpr d e m fe' dimInv dimLe)

  | ASTFE_VAR_STRUCT sB sType sField sVar ⇒
   ASTFE_VAR_STRUCT fe' sB sType sField (ast_to_astfe_retype_var fe sB (AST_TYPE_STRUCT sType) sVar d e m fe' dimInv dimLe)                                                                                    
  ]
and ast_to_astfe_retype_base_expr fe (ast:astfe_base_expr fe)
                                  d (e:aux_env_type d) (m:aux_map_type d) fe'
                                  (dimInv:env_to_flatEnv_inv d e m fe') (dimLe:le_flatEnv fe fe' = true) on ast : astfe_base_expr fe' ≝
 match ast
  return λa:astfe_base_expr fe.astfe_base_expr fe'
 with
  [ ASTFE_BASE_EXPR bType sExpr ⇒
   ASTFE_BASE_EXPR fe' bType (ast_to_astfe_retype_expr fe (AST_TYPE_BASE bType) sExpr d e m fe' dimInv dimLe)
  ].

(*
  AST_INIT_VAR: ∀b:bool.∀t:ast_type.
                ast_var d e b t → ast_init d e t
| AST_INIT_VAL: ∀t:ast_type.
                aux_ast_init_type t → ast_init d e t
*)
definition ast_to_astfe_init ≝
λd.λe:aux_env_type d.λt.λast:ast_init d e t.
λm:aux_map_type d.λfe.
λdimInv:env_to_flatEnv_inv d e m fe.
 match ast
  return λW.λa:ast_init d e W.astfe_init fe W
 with
  [ AST_INIT_VAR sB sType sVar ⇒
   ASTFE_INIT_VAR fe sB sType (ast_to_astfe_var d e sB sType sVar m fe dimInv)

  | AST_INIT_VAL sType sArgs ⇒
   ASTFE_INIT_VAL fe sType sArgs

  ].

definition ast_to_astfe_retype_init ≝
λfe,t.λast:astfe_init fe t.
λd.λe:aux_env_type d.λm:aux_map_type d.λfe'.
λdimInv:env_to_flatEnv_inv d e m fe'.
λdimLe:le_flatEnv fe fe' = true.
 match ast
  return λW.λa:astfe_init fe W.astfe_init fe' W
 with
  [ ASTFE_INIT_VAR sB sType sVar ⇒
   ASTFE_INIT_VAR fe' sB sType (ast_to_astfe_retype_var fe sB sType sVar d e m fe' dimInv dimLe)

  | ASTFE_INIT_VAL sType sArgs ⇒
   ASTFE_INIT_VAL fe' sType sArgs

  ].

(*
  ASTFE_STM_ASG: ∀t:ast_type.
                 astfe_var e false t → astfe_expr e t → astfe_stm e
| ASTFE_STM_INIT: ∀b:bool.∀t:ast_type.
                  astfe_id e b t → astfe_init e t → astfe_stm e
| ASTFE_STM_WHILE: astfe_base_expr e → astfe_body e → astfe_stm e
| ASTFE_STM_IF: ne_list (Prod (astfe_base_expr e) (astfe_body e)) → option (astfe_body e) → astfe_stm e
*)
let rec ast_to_astfe_retype_stm fe (ast:astfe_stm fe)
                                d (e:aux_env_type d) (m:aux_map_type d) fe'
                                (dimInv:env_to_flatEnv_inv d e m fe') (dimLe:le_flatEnv fe fe' = true) on ast : astfe_stm fe' ≝
 match ast with
  [ ASTFE_STM_ASG sType sVar sExpr ⇒
   ASTFE_STM_ASG fe' sType (ast_to_astfe_retype_var fe false sType sVar d e m fe' dimInv dimLe)
                           (ast_to_astfe_retype_expr fe sType sExpr d e m fe' dimInv dimLe)

  | ASTFE_STM_INIT sB sType sId sInit ⇒
   ASTFE_STM_INIT fe' sB sType (ast_to_astfe_retype_id fe sB sType sId d e m fe' dimInv dimLe)
                               (ast_to_astfe_retype_init fe sType sInit d e m fe' dimInv dimLe)

  | ASTFE_STM_WHILE sExpr sBody ⇒
   ASTFE_STM_WHILE fe' (ast_to_astfe_retype_base_expr fe sExpr d e m fe' dimInv dimLe)
                       (ast_to_astfe_retype_body fe sBody d e m fe' dimInv dimLe)

  | ASTFE_STM_IF sNelExprBody sOptBody ⇒
   ASTFE_STM_IF fe' (cut_last_neList ? (fold_right_neList ?? (λh,t.«£(pair ?? (ast_to_astfe_retype_base_expr fe (fst ?? h) d e m fe' dimInv dimLe)
                                                                              (ast_to_astfe_retype_body fe (snd ?? h) d e m fe' dimInv dimLe)
                                                                              )»&t)
                                                             «£(pair ?? (ASTFE_BASE_EXPR fe' (AST_BASE_TYPE_BYTE8) (ASTFE_EXPR_BYTE8 fe' 〈x0,x0〉)) (ASTFE_BODY fe' []))»
                                                             sNelExprBody))
                    (opt_map ?? sOptBody
                      (λsBody.Some ? (ast_to_astfe_retype_body fe sBody d e m fe' dimInv dimLe)))
  ]
(*
  ASTFE_BODY: list (astfe_stm e) → astfe_body e
*)
and ast_to_astfe_retype_body fe (ast:astfe_body fe)
                             d (e:aux_env_type d) (m:aux_map_type d) fe'
                             (dimInv:env_to_flatEnv_inv d e m fe') (dimLe:le_flatEnv fe fe' = true) on ast : astfe_body fe' ≝
 match ast with
  [ ASTFE_BODY sLStm ⇒
   ASTFE_BODY fe' (fold_right_list ?? (λh,t.[ ast_to_astfe_retype_stm fe h d e m fe' dimInv dimLe ]@t) [] sLStm)
  ].

definition ast_to_astfe_retype_stm_list ≝
λfe.λast:list (astfe_stm fe).
λd.λe:aux_env_type d.λm:aux_map_type d.λfe'.
λdimInv:env_to_flatEnv_inv d e m fe'.
λdimLe:le_flatEnv fe fe' = true.
 fold_right_list ?? (λh,t.[ ast_to_astfe_retype_stm fe h d e m fe' dimInv dimLe ]@t) [] ast.

definition ast_to_astfe_retype_exprBody_neList ≝
λfe.λast:ne_list (Prod (astfe_base_expr fe) (astfe_body fe)).
λd.λe:aux_env_type d.λm:aux_map_type d.λfe'.
λdimInv:env_to_flatEnv_inv d e m fe'.
λdimLe:le_flatEnv fe fe' = true.
 cut_last_neList ? (fold_right_neList ?? (λh,t.«£(pair ?? (ast_to_astfe_retype_base_expr fe (fst ?? h) d e m fe' dimInv dimLe)
                                                          (ast_to_astfe_retype_body fe (snd ?? h) d e m fe' dimInv dimLe)
                                                          )»&t)
                                         «£(pair ?? (ASTFE_BASE_EXPR fe' (AST_BASE_TYPE_BYTE8) (ASTFE_EXPR_BYTE8 fe' 〈x0,x0〉)) (ASTFE_BODY fe' []))»
                                         ast).

(* multi-sigma per incapsulare i risultati della trasformazione sugli stm/decl *)
inductive ast_to_astfe_stm_record (d:nat) (e:aux_env_type d) (fe:aux_flatEnv_type) : Type ≝
AST_TO_ASTFE_STM_RECORD: ∀m:aux_map_type d.∀fe'.
                         env_to_flatEnv_inv d e m fe' →
                         le_flatEnv fe fe' = true →
                         astfe_stm fe' →
                         ast_to_astfe_stm_record d e fe.

inductive ast_to_astfe_if_record (d:nat) (e:aux_env_type d) (fe:aux_flatEnv_type) : Type ≝
AST_TO_ASTFE_IF_RECORD: ∀m:aux_map_type d.∀fe'.
                        env_to_flatEnv_inv d e m fe' →
                        le_flatEnv fe fe' = true →
                        ne_list (Prod (astfe_base_expr fe') (astfe_body fe')) →
                        ast_to_astfe_if_record d e fe.

inductive ast_to_astfe_decl_record (d:nat) (e:aux_env_type d) (fe:aux_flatEnv_type) : Type ≝
AST_TO_ASTFE_DECL_RECORD: ∀m:aux_map_type d.∀fe'.∀trsf:list (Prod3T aux_str_type bool ast_type).
                          env_to_flatEnv_inv d (build_trasfEnv_env d trsf e) m fe' →
                          le_flatEnv fe fe' = true →
                          list (astfe_stm fe') →
                          ast_to_astfe_decl_record d e fe.

inductive ast_to_astfe_decl_aux_record (d:nat) (e:aux_env_type d) (fe:aux_flatEnv_type) : Type ≝
AST_TO_ASTFE_DECL_AUX_RECORD: ∀m:aux_map_type d.∀fe'.
                              env_to_flatEnv_inv d e m fe' →
                              le_flatEnv fe fe' = true →
                              list (astfe_stm fe') →
                              ast_to_astfe_decl_aux_record d e fe.

(*
  AST_STM_ASG: ∀d.∀e:aux_env_type d.∀t:ast_type.
               ast_var d e false t → ast_expr d e t → ast_stm d e
| AST_STM_WHILE: ∀d.∀e:aux_env_type d.
                 ast_base_expr d e → ast_decl (S d) (enter_env d e) → ast_stm d e
| AST_STM_IF: ∀d.∀e:aux_env_type d.
              ne_list (Prod (ast_base_expr d e) (ast_decl (S d) (enter_env d e))) → option (ast_decl (S d) (enter_env d e)) → ast_stm d e
*)
let rec ast_to_astfe_stm d (e:aux_env_type d) (ast:ast_stm d e) on ast : Πm:aux_map_type d.Πfe.
                                                                         env_to_flatEnv_inv d e m fe →
                                                                         ast_to_astfe_stm_record d e fe ≝
 match ast
  return λD.λE.λast:ast_stm D E.
         Πm:aux_map_type D.Πfe.env_to_flatEnv_inv D E m fe → ast_to_astfe_stm_record D E fe
 with
  [ AST_STM_ASG sD sE sType sVar sExpr ⇒
   λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
   AST_TO_ASTFE_STM_RECORD sD sE fe m fe dimInv
                           (eq_to_leflatenv ?? (refl_eq ??))
                           (ASTFE_STM_ASG fe sType (ast_to_astfe_var sD sE false sType sVar m fe dimInv)
                                                   (ast_to_astfe_expr sD sE sType sExpr m fe dimInv))
  | AST_STM_WHILE sD sE sExpr sDecl ⇒
   λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
   match ast_to_astfe_decl (S sD) (enter_env sD sE) sDecl (enter_map sD m) fe
         (env_map_flatEnv_enter_aux sD sE m fe dimInv) with
    [ AST_TO_ASTFE_DECL_RECORD resMap resFe resTrsf resDimInv resDimLe resLStm ⇒
     eq_rect ? (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
             (λenv.ast_to_astfe_stm_record sD env fe)
             (AST_TO_ASTFE_STM_RECORD sD
                                      (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                      fe
                                      (leave_map sD resMap)
                                      resFe
                                      (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap resFe resTrsf resDimInv)
                                      resDimLe
                                      (ASTFE_STM_WHILE resFe
                                                       (ast_to_astfe_retype_base_expr fe (ast_to_astfe_base_expr sD sE sExpr m fe dimInv)
                                                                                      sD
                                                                                      (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                                                                      (leave_map sD resMap)
                                                                                      resFe
                                                                                      (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap resFe resTrsf resDimInv)
                                                                                      resDimLe)                                                       
                                                       (ASTFE_BODY resFe resLStm)))                       
             sE (leave_add_enter_env sD sE resTrsf) ]

  | AST_STM_IF sD sE sExprDecl sOptDecl ⇒
   λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
   let rec aux (nel:ne_list (Prod (ast_base_expr sD sE) (ast_decl (S sD) (enter_env sD sE))))
               (pMap:aux_map_type sD) (pFe:aux_flatEnv_type)
               (pDimInv:env_to_flatEnv_inv sD sE pMap pFe) on nel : ast_to_astfe_if_record sD sE pFe ≝
    match nel with
     [ ne_nil h ⇒
      match ast_to_astfe_decl (S sD) (enter_env sD sE) (snd ?? h) (enter_map sD pMap) pFe
            (env_map_flatEnv_enter_aux sD sE pMap pFe pDimInv) with
       [ AST_TO_ASTFE_DECL_RECORD resMap resFe resTrsf resDimInv resDimLe resLStm ⇒
        eq_rect ? (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                (λenv.ast_to_astfe_if_record sD env pFe)
                (AST_TO_ASTFE_IF_RECORD sD
                                        (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                        pFe
                                        (leave_map sD resMap)
                                        resFe
                                        (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap resFe resTrsf resDimInv)
                                        resDimLe
                                        «£(pair ?? (ast_to_astfe_retype_base_expr pFe (ast_to_astfe_base_expr sD sE (fst ?? h) pMap pFe pDimInv)
                                                                                  sD
                                                                                  (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                                                                  (leave_map sD resMap)
                                                                                  resFe
                                                                                  (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap resFe resTrsf resDimInv)
                                                                                  resDimLe)
                                                   (ASTFE_BODY resFe resLStm))»)
                sE (leave_add_enter_env sD sE resTrsf) ]

     | ne_cons h t ⇒
      match ast_to_astfe_decl (S sD) (enter_env sD sE) (snd ?? h) (enter_map sD pMap) pFe
            (env_map_flatEnv_enter_aux sD sE pMap pFe pDimInv) with
       [ AST_TO_ASTFE_DECL_RECORD resMap resFe resTrsf resDimInv resDimLe resLStm ⇒
        match aux t (leave_map sD resMap) resFe
                  (eq_rect ? (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                           (λenv.env_to_flatEnv_inv sD env (leave_map sD resMap) resFe)
                           (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap resFe resTrsf resDimInv)
                           sE (leave_add_enter_env sD sE resTrsf)) with
        [ AST_TO_ASTFE_IF_RECORD resMap' resFe' resDimInv' resDimLe' resExprBody ⇒
         AST_TO_ASTFE_IF_RECORD sD sE pFe resMap' resFe' resDimInv'
                                (leflatenv_trans ??? resDimLe resDimLe')
                                («£(pair ?? (ast_to_astfe_retype_base_expr pFe (ast_to_astfe_base_expr sD sE (fst ?? h) pMap pFe pDimInv)
                                                                           sD sE resMap' resFe' resDimInv'
                                                                           (leflatenv_trans ??? resDimLe resDimLe'))
                                            (ast_to_astfe_retype_body resFe (ASTFE_BODY resFe resLStm)
                                                                      sD sE resMap' resFe' resDimInv' resDimLe'))»&resExprBody) ]]

     ] in
   match aux sExprDecl m fe dimInv with
    [ AST_TO_ASTFE_IF_RECORD resMap resFe resDimInv resDimLe resExprBody ⇒
     match sOptDecl with
      [ None ⇒
       AST_TO_ASTFE_STM_RECORD sD sE fe resMap resFe resDimInv resDimLe (ASTFE_STM_IF resFe resExprBody (None ?))

      | Some sDecl ⇒
       match ast_to_astfe_decl (S sD) (enter_env sD sE) sDecl (enter_map sD resMap) resFe
             (env_map_flatEnv_enter_aux sD sE resMap resFe resDimInv) with
        [ AST_TO_ASTFE_DECL_RECORD resMap' resFe' resTrsf resDimInv' resDimLe' resLStm ⇒
         eq_rect ? (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                 (λenv.ast_to_astfe_stm_record sD env fe)
                 (AST_TO_ASTFE_STM_RECORD sD
                                          (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                          fe
                                          (leave_map sD resMap')
                                          resFe'
                                          (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap' resFe' resTrsf resDimInv')
                                          (leflatenv_trans ??? resDimLe resDimLe')
                                          (ASTFE_STM_IF resFe'
                                                        (ast_to_astfe_retype_exprBody_neList resFe resExprBody
                                                                                             sD
                                                                                             (leave_env sD (build_trasfEnv_env (S sD) resTrsf (enter_env sD sE)))
                                                                                             (leave_map sD resMap')
                                                                                             resFe'
                                                                                             (env_map_flatEnv_leave_aux sD (enter_env sD sE) resMap' resFe' resTrsf resDimInv')
                                                                                             resDimLe')
                                                        (Some ? (ASTFE_BODY resFe' resLStm))))
                 sE (leave_add_enter_env sD sE resTrsf) ]]]

  ]
(*
  AST_NO_DECL: ∀d.∀e:aux_env_type d.
               list (ast_stm d e) → ast_decl d e
| AST_CONST_DECL: ∀d.∀e:aux_env_type d.∀str:aux_str_type.∀t:ast_type.
                  (check_not_already_def_env d e str) → ast_init d e t → ast_decl d (add_desc_env d e str true t) → ast_decl d e
| AST_VAR_DECL: ∀d.∀e:aux_env_type d.∀str:aux_str_type.∀t:ast_type.
                (check_not_already_def_env d e str) → option (ast_init d e t) → ast_decl d (add_desc_env d e str false t) → ast_decl d e
*)
and ast_to_astfe_decl d (e:aux_env_type d) (ast:ast_decl d e) on ast : Πm:aux_map_type d.Πfe.
                                                                       env_to_flatEnv_inv d e m fe →
                                                                       ast_to_astfe_decl_record d e fe ≝
 match ast
  return λD.λE.λast:ast_decl D E.
         Πm:aux_map_type D.Πfe.env_to_flatEnv_inv D E m fe → ast_to_astfe_decl_record D E fe
  with
   [ AST_NO_DECL sD sE sLStm ⇒
    λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
    let rec aux (l:list (ast_stm sD sE)) (pMap:aux_map_type sD) (pFe:aux_flatEnv_type)
                (pDimInv:env_to_flatEnv_inv sD sE pMap pFe) on l : ast_to_astfe_decl_aux_record sD sE pFe ≝
     match l with
      [ nil ⇒
       AST_TO_ASTFE_DECL_AUX_RECORD sD sE pFe pMap pFe pDimInv (eq_to_leflatenv ?? (refl_eq ??)) []

      | cons h t ⇒
       match ast_to_astfe_stm sD sE h pMap pFe pDimInv with
        [ AST_TO_ASTFE_STM_RECORD resMap resFe resDimInv resDimLe resStm ⇒
         match aux t resMap resFe resDimInv with
          [ AST_TO_ASTFE_DECL_AUX_RECORD resMap' resFe' resDimInv' resDimLe' resLStm ⇒
           AST_TO_ASTFE_DECL_AUX_RECORD sD sE pFe resMap' resFe' resDimInv'
                                        (leflatenv_trans ??? resDimLe resDimLe')
                                        ([ ast_to_astfe_retype_stm resFe resStm sD sE resMap' resFe' resDimInv' resDimLe' ]@resLStm) ]]

      ] in
   match aux sLStm m fe dimInv with
    [ AST_TO_ASTFE_DECL_AUX_RECORD resMap resFe resDimInv resDimLe resLStm ⇒
     AST_TO_ASTFE_DECL_RECORD sD sE fe resMap resFe []
                              (env_map_flatEnv_addNil_aux sD sE resMap resFe resDimInv)
                              resDimLe resLStm ]

   | AST_CONST_DECL sD sE sName sType sDim sInit sDecl ⇒
    λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
    match ast_to_astfe_decl sD (add_desc_env sD sE sName true sType) sDecl
          (fst ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName true sType ] (pair ?? m fe)))
          (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName true sType ] (pair ?? m fe)))
          (env_map_flatEnv_addSingle_aux sD sE m fe sName true sType dimInv) with
     [ AST_TO_ASTFE_DECL_RECORD resMap resFe resTrsf resDimInv resDimLe resLStm ⇒
      AST_TO_ASTFE_DECL_RECORD sD sE fe resMap resFe
                               ([ tripleT ??? sName true sType ]@resTrsf)
                               (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName true sType resTrsf resDimInv)
                               (leflatenv_trans ??? (buildtrasfenvadd_to_le sD m fe [ tripleT ??? sName true sType ]) resDimLe)
                               ([ ASTFE_STM_INIT resFe true sType
                                                 (* l'id e' sull'ambiente arricchito *)
                                                 (ast_to_astfe_retype_id (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName true sType ] (pair ?? m fe)))
                                                                         true sType
                                                                         (ast_to_astfe_id sD (add_desc_env sD sE sName true sType)
                                                                                          true sType
                                                                                          (newid_from_init sD sE sName true sType)
                                                                                          (fst ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName true sType ] (pair ?? m fe)))
                                                                                          (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName true sType ] (pair ?? m fe)))
                                                                                          (env_map_flatEnv_addSingle_aux sD sE m fe sName true sType dimInv))
                                                                         sD (build_trasfEnv_env sD ([ tripleT ??? sName true sType ]@resTrsf) sE)
                                                                         resMap resFe
                                                                         (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName true sType resTrsf resDimInv)
                                                                         resDimLe)
                                                 (* l'init e' sull'ambiente non arricchito *)
                                                 (ast_to_astfe_retype_init fe sType (ast_to_astfe_init sD sE sType sInit m fe dimInv)
                                                                           sD (build_trasfEnv_env sD ([ tripleT ??? sName true sType ]@resTrsf) sE)
                                                                           resMap resFe
                                                                           (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName true sType resTrsf resDimInv)
                                                                           (leflatenv_trans ??? (buildtrasfenvadd_to_le sD m fe [ tripleT ??? sName true sType ]) resDimLe))
                                ]@resLStm) ]

   | AST_VAR_DECL sD sE sName sType sDim sOptInit sDecl ⇒
    λm:aux_map_type sD.λfe.λdimInv:env_to_flatEnv_inv sD sE m fe.
    match ast_to_astfe_decl sD (add_desc_env sD sE sName false sType) sDecl
          (fst ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName false sType ] (pair ?? m fe)))
          (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName false sType ] (pair ?? m fe)))
          (env_map_flatEnv_addSingle_aux sD sE m fe sName false sType dimInv) with
     [ AST_TO_ASTFE_DECL_RECORD resMap resFe resTrsf resDimInv resDimLe resLStm ⇒
      AST_TO_ASTFE_DECL_RECORD sD sE fe resMap resFe
                               ([ tripleT ??? sName false sType ]@resTrsf)
                               (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName false sType resTrsf resDimInv)
                               (leflatenv_trans ??? (buildtrasfenvadd_to_le sD m fe [ tripleT ??? sName false sType ]) resDimLe)
                               (match sOptInit with
                                [ None ⇒ []
                                | Some init ⇒
                                 [ ASTFE_STM_INIT resFe false sType
                                                  (* l'id e' sull'ambiente arricchito *)
                                                  (ast_to_astfe_retype_id (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName false sType ] (pair ?? m fe)))
                                                                          false sType
                                                                          (ast_to_astfe_id sD (add_desc_env sD sE sName false sType)
                                                                                           false sType
                                                                                           (newid_from_init sD sE sName false sType)
                                                                                           (fst ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName false sType ] (pair ?? m fe)))
                                                                                           (snd ?? (build_trasfEnv_mapFe sD [ tripleT ??? sName false sType ] (pair ?? m fe)))
                                                                                           (env_map_flatEnv_addSingle_aux sD sE m fe sName false sType dimInv))
                                                                          sD (build_trasfEnv_env sD ([ tripleT ??? sName false sType ]@resTrsf) sE)
                                                                          resMap resFe
                                                                          (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName false sType resTrsf resDimInv)
                                                                          resDimLe)
                                                  (* l'init e' sull'ambiente non arricchito *)
                                                  (ast_to_astfe_retype_init fe sType (ast_to_astfe_init sD sE sType init m fe dimInv)
                                                                            sD (build_trasfEnv_env sD ([ tripleT ??? sName false sType ]@resTrsf) sE)
                                                                            resMap resFe
                                                                            (env_map_flatEnv_addJoin_aux sD sE resMap resFe sName false sType resTrsf resDimInv)
                                                                            (leflatenv_trans ??? (buildtrasfenvadd_to_le sD m fe [ tripleT ??? sName false sType ]) resDimLe))
                                 ]]@resLStm) ]          

   ].

(*
  AST_ROOT: ast_decl O empty_env → ast_root
*)
definition ast_to_astfe : ast_root → (Σfe.astfe_root fe) ≝
λast:ast_root.match ast with
 [ AST_ROOT decl ⇒ match ast_to_astfe_decl O empty_env decl empty_map empty_flatEnv env_map_flatEnv_empty_aux with
  [ AST_TO_ASTFE_DECL_RECORD _ resFe _ _ _ resLStm ⇒ ≪resFe,ASTFE_ROOT resFe (ASTFE_BODY resFe resLStm)≫ ]].
