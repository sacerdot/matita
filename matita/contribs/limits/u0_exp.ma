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

include "u0_class.ma".

(* EXPONENTIAL CLASS **************************************************)

definition u0_exp_eq (D,C): u0_predicate2 (u0_fun D C) ≝
                     λf,g. (u0_xeq … (u0_class_in D) … (u0_class_eq C) f g).

definition u0_exp (D,C): u0_class ≝
                  mk_u0_class (u0_fun D C) (is_u0_fun …) (u0_exp_eq D C).

definition u0_proj1 (D1,D2): u0_fun D1 (u0_exp D2 D1) ≝
                    mk_u0_fun … (λa. mk_u0_fun … (u0_k … a)).

(* Basic properties ***************************************************)

lemma u0_class_exp: ∀D,C. is_u0_class C → is_u0_class (u0_exp D C).
/4 width=7 by mk_is_u0_class, u0_class_refl, u0_class_repl, u0_fun_hom1/ qed.

lemma u0_fun_proj1: ∀D2,D1. is_u0_class D1 → is_u0_fun … (u0_proj1 D1 D2).
#D2 #D1 #HD1 @mk_is_u0_fun /3 width=1 by mk_is_u0_fun, u0_class_refl/
qed.
