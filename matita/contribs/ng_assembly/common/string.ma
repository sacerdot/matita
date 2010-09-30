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

include "common/ascii.ma".
include "common/list_utility.ma".

(* ************************ *)
(* MANIPOLAZIONE DI STRINGA *)
(* ************************ *)

(* tipo pubblico *)
ndefinition aux_str_type ≝ list ascii.

(* strcmp *)
ndefinition eq_str ≝
 bfold_right_list2 ascii (λx,y.eq_ascii x y).

(* ************ *)
(* STRINGA + ID *)
(* ************ *)

(* tipo pubblico *)
nrecord strId : Type ≝
 {
 str_elem: aux_str_type;
 id_elem: nat
 }.

(* confronto *)
ndefinition eq_strId ≝
λsid,sid':strId.
 (eq_str (str_elem sid) (str_elem sid'))⊗
 (eq_nat (id_elem sid) (id_elem sid')).
