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

include "common/list_utility.ma".

(* ************************* *)
(* dimensioni degli elementi *)
(* ************************* *)

(* usato per definire nell'ast *)
ninductive ast_base_type : Type ≝
  AST_BASE_TYPE_BYTE8: ast_base_type
| AST_BASE_TYPE_WORD16: ast_base_type
| AST_BASE_TYPE_WORD32: ast_base_type.

ninductive ast_type : Type ≝
  AST_TYPE_BASE: ast_base_type → ast_type
| AST_TYPE_ARRAY: ast_type → nat → ast_type
| AST_TYPE_STRUCT: ne_list ast_type → ast_type.

(* principio di eliminazione arricchito *)
nlet rec ast_type_index_aux (P:ast_type → Prop)
                            (f:Πt.P t → P (AST_TYPE_STRUCT (ne_nil ? t)))
                            (f1:Πh,t.P h → P (AST_TYPE_STRUCT t) → P (AST_TYPE_STRUCT (ne_cons ? h t)))
                            (f2:Πt.P t)
                            (t:ne_list ast_type) on t ≝
 match t return λt.P (AST_TYPE_STRUCT t) with
  [ ne_nil h ⇒ f h (f2 h)
  | ne_cons h t ⇒ f1 h t (f2 h) (ast_type_index_aux P f f1 f2 t)
  ].

nlet rec ast_type_index (P:ast_type → Prop)
                        (f:Πb.P (AST_TYPE_BASE b))
                        (f1:Πt,n.P t → P (AST_TYPE_ARRAY t n))
                        (f2:Πt.P t → P (AST_TYPE_STRUCT (ne_nil ? t)))
                        (f3:Πh,t.P h → P (AST_TYPE_STRUCT t) → P (AST_TYPE_STRUCT (ne_cons ? h t)))
                        (t:ast_type) on t : P t ≝
 match t return λt.P t with
  [ AST_TYPE_BASE b ⇒ f b
  | AST_TYPE_ARRAY t' n ⇒ f1 t' n (ast_type_index P f f1 f2 f3 t')
  | AST_TYPE_STRUCT nl ⇒ match nl with
   [ ne_nil h ⇒ f2 h (ast_type_index P f f1 f2 f3 h)
   | ne_cons h t ⇒ f3 h t (ast_type_index P f f1 f2 f3 h) (ast_type_index_aux P f2 f3 (ast_type_index P f f1 f2 f3) t)
   ]
  ]. 

nlet rec ast_type_rectex_aux (P:ast_type → Type)
                             (f:Πt.P t → P (AST_TYPE_STRUCT (ne_nil ? t)))
                             (f1:Πh,t.P h → P (AST_TYPE_STRUCT t) → P (AST_TYPE_STRUCT (ne_cons ? h t)))
                             (f2:Πt.P t)
                             (t:ne_list ast_type) on t ≝
 match t return λt.P (AST_TYPE_STRUCT t) with
  [ ne_nil h ⇒ f h (f2 h)
  | ne_cons h t ⇒ f1 h t (f2 h) (ast_type_rectex_aux P f f1 f2 t)
  ].

nlet rec ast_type_rectex (P:ast_type → Type)
                         (f:Πb.P (AST_TYPE_BASE b))
                         (f1:Πt,n.P t → P (AST_TYPE_ARRAY t n))
                         (f2:Πt.P t → P (AST_TYPE_STRUCT (ne_nil ? t)))
                         (f3:Πh,t.P h → P (AST_TYPE_STRUCT t) → P (AST_TYPE_STRUCT (ne_cons ? h t)))
                         (t:ast_type) on t : P t ≝
 match t return λt.P t with
  [ AST_TYPE_BASE b ⇒ f b
  | AST_TYPE_ARRAY t' n ⇒ f1 t' n (ast_type_rectex P f f1 f2 f3 t')
  | AST_TYPE_STRUCT nl ⇒ match nl with
   [ ne_nil h ⇒ f2 h (ast_type_rectex P f f1 f2 f3 h)
   | ne_cons h t ⇒ f3 h t (ast_type_rectex P f f1 f2 f3 h) (ast_type_rectex_aux P f2 f3 (ast_type_rectex P f f1 f2 f3) t)
   ]
  ]. 

ndefinition eq_astbasetype ≝
λt1,t2:ast_base_type.match t1 with
 [ AST_BASE_TYPE_BYTE8 ⇒ match t2 with [ AST_BASE_TYPE_BYTE8 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD16 ⇒ match t2 with [ AST_BASE_TYPE_WORD16 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD32 ⇒ match t2 with [ AST_BASE_TYPE_WORD32 ⇒ true | _ ⇒ false ]
 ].

nlet rec eq_asttype (t1,t2:ast_type) on t1 ≝
 match t1 with
  [ AST_TYPE_BASE bType1 ⇒ match t2 with
   [ AST_TYPE_BASE bType2 ⇒ eq_astbasetype bType1 bType2
   | _ ⇒ false ]
  | AST_TYPE_ARRAY subType1 dim1 ⇒ match t2 with
   [ AST_TYPE_ARRAY subType2 dim2 ⇒ (eq_asttype subType1 subType2) ⊗ (eq_nat dim1 dim2)
   | _ ⇒ false ]
  | AST_TYPE_STRUCT nelSubType1 ⇒ match t2 with
   [ AST_TYPE_STRUCT nelSubType2 ⇒ bfold_right_neList2 ? (λx1,x2.eq_asttype x1 x2) nelSubType1 nelSubType2
   | _ ⇒ false
   ]
  ].

ndefinition is_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ True | _ ⇒ False ].

ndefinition isb_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ true | _ ⇒ false ].

ndefinition isnt_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ False | _ ⇒ True ].

ndefinition isntb_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ false | _ ⇒ true ].

ndefinition eval_size_base_type ≝
λast:ast_base_type.match ast with
 [ AST_BASE_TYPE_BYTE8 ⇒ nat1
 | AST_BASE_TYPE_WORD16 ⇒ nat2
 | AST_BASE_TYPE_WORD32 ⇒ nat4
 ].

nlet rec eval_size_type (ast:ast_type) on ast ≝
 match ast with
  [ AST_TYPE_BASE b ⇒ eval_size_base_type b
  | AST_TYPE_ARRAY sub_ast dim ⇒ (dim + nat1)*(eval_size_type sub_ast)
  | AST_TYPE_STRUCT nel_ast ⇒ fold_right_neList … (λt,x.(eval_size_type t)+x) O nel_ast
  ].
