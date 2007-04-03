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

definition step ≝ λa,b,c:T.λH1:a=b.λH2:a=c. eq_ind T ? (λx.b = x) H1 ? H2.

lemma stepH : ∀a:T.∀H:a=a. step ? ? ? H H = refl_eq T a.
intros (a H); cases H; reflexivity.
qed.

axiom decT : ∀a,b:T. a = b ∨ a ≠ b.

lemma nu : ∀a,b:T. ∀E:a=b. a=b.
intros (a b E); cases (decT a b) (Ecanonical Abs); [ exact H | cases (H E) ]
qed.

lemma nu_k : ∀a,b:T. ∀E1,E2:a=b. nu ? ? E1 = nu ? ? E2.
intros (a b E1 E2); unfold nu; 
cases (decT a b); simplify; [ reflexivity | cases (H E1) ]
qed.

definition nu_inv ≝ λa,b:T. λE:a=b. step ? ? ? (nu ? ? (refl_eq ? a)) E. 

definition cancel ≝ λA,B:Type.λf.λg:A→B.∀x:A.f (g x) = x.

lemma cancel_nu_nu_inv : ∀a,b:T. cancel (a=b) (a=b) (nu_inv a b) (nu a b).
intros (a b); unfold cancel; intros (E); cases E;
unfold nu_inv; rewrite > stepH; reflexivity.
qed.

lemma pirrel :  ∀a,b:T.∀E1,E2:a=b. E1 = E2.
intros (a b E1 E2);
rewrite < cancel_nu_nu_inv; 
rewrite < cancel_nu_nu_inv in ⊢ (? ? ? %);
rewrite > (nu_k ? ? E1 E2).
reflexivity.
qed.

(* some more tests *)
inductive eq4 (A : Type) (x : A) (y : A) : A → A → Prop ≝ 
  eq_refl4 : eq4 A x y x y.
  
lemma step4 : ∀a,b:T.∀H:eq4 T a b a b. 
  eq4_ind T a b (λx,y.eq4 T x y a b) H a b H = eq_refl4 T a b.
intros (a b H). cases H. reflexivity.
qed.
