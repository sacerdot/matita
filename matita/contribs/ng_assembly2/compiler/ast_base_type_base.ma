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

include "num/bool.ma".

(* ************************* *)
(* dimensioni degli elementi *)
(* ************************* *)

(* usato per definire nell'ast *)
ninductive ast_base_type : Type ≝
  AST_BASE_TYPE_BYTE8: ast_base_type
| AST_BASE_TYPE_WORD16: ast_base_type
| AST_BASE_TYPE_WORD32: ast_base_type.

(* iteratore *)
ndefinition forall_astbasetype ≝ λP.
 P AST_BASE_TYPE_BYTE8 ⊗
 P AST_BASE_TYPE_WORD16 ⊗
 P AST_BASE_TYPE_WORD32.

ndefinition eq_astbasetype ≝
λt1,t2:ast_base_type.match t1 with
 [ AST_BASE_TYPE_BYTE8 ⇒ match t2 with [ AST_BASE_TYPE_BYTE8 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD16 ⇒ match t2 with [ AST_BASE_TYPE_WORD16 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD32 ⇒ match t2 with [ AST_BASE_TYPE_WORD32 ⇒ true | _ ⇒ false ]
 ].

