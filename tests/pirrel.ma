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

set "baseuri" "cic:/matita/test/".

include "logic/connectives.ma".
include "logic/equality.ma".

axiom T : Type.

lemma step : ∀a:T.∀H:a=a. eq_ind T a (λx.a = x) H a (sym_eq ? ? ? H) = refl_eq T a.
intros (a H). cases H. reflexivity.
qed.

inductive eq4 (A : Type) (x : A) (y : A) : A → A → Prop ≝ 
  eq_refl4 : eq4 A x y x y.
  
lemma step4 : ∀a,b:T.∀H:eq4 T a b a b. 
  eq4_ind T a b (λx,y.eq4 T x y a b) H a b H = eq_refl4 T a b.
intros (a b H). cases H. reflexivity.
qed.

