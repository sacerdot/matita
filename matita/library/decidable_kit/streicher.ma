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

include "logic/connectives.ma".
include "logic/equality.ma".

definition step ≝ λT:Type.λa,b,c:T.λH1:a=b.λH2:a=c. eq_ind T ? (λx.b = x) H1 ? H2.

lemma stepH : ∀T:Type.∀a:T.∀H:a=a. step ? ? ? ? H H = refl_eq T a.
intros (T a H); cases H; reflexivity.
qed.

definition decT ≝ λT:Type.∀x,y:T. decidable (x=y).

lemma nu : ∀T:Type.∀a,b:T. decT T → ∀E:a=b. a=b.
intros (T a b decT E); cases (decT a b) (Ecanonical Abs); [ exact Ecanonical | cases (Abs E) ]
qed.

lemma nu_k : ∀T:Type.∀a,b:T.∀E1,E2:a=b. ∀d : decT T. nu ? ? ? d E1 = nu ? ? ? d E2.
intros (T a b E1 E2 decT); unfold nu; 
cases (decT a b); simplify; [ reflexivity | cases (H E1) ]
qed.

definition nu_inv ≝ λT:Type.λa,b:T. λd: decT T.λE:a=b. 
  step ? ? ? ? (nu ? ? ? d (refl_eq ? a)) E. 

definition cancel ≝ λT:Type.λA,B:Type.λf.λg:A→B.∀x:A.f (g x) = x.

(* non inferisce Prop?!??! *)
lemma cancel_nu_nu_inv : ∀T:Type.∀a,b:T.∀d: decT T. 
  cancel Prop (a=b) (a=b) (nu_inv ? a b d) (nu ? a b d).
intros (T a b); unfold cancel; intros (E); cases E;
unfold nu_inv; rewrite > stepH; reflexivity.
qed.

theorem pirrel :  ∀T:Type.∀a,b:T.∀E1,E2:a=b.∀d: decT T. E1 = E2.
intros (T a b E1 E2 decT);
rewrite < (cancel_nu_nu_inv ? ? ? decT); 
rewrite < (cancel_nu_nu_inv ? ? ? decT) in ⊢ (? ? ? %);
rewrite > (nu_k ? ? ? E1 E2 decT).
reflexivity.
qed.

