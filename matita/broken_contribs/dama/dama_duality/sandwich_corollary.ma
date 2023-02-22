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

include "sandwich.ma".

(* 3.17 *)
lemma tends_uniq:
  ∀R.∀ml:mlattice R.∀xn:sequence ml.∀x,y:ml. 
     xn ⇝ x → xn ⇝ y → δ x y ≈ 0.
intros (R ml xn x y H1 H2); unfold tends0 in H1 H2; unfold d2s in H1 H2;
intro Axy; lapply (ap_le_to_lt ??? (ap_symmetric ??? Axy) (mpositive ? ml ??)) as ge0;
cases (H1 (δ x y/1) (divide_preserves_lt ??? ge0)) (n1 Hn1); clear H1; 
cases (H2 (δ x y/1) (divide_preserves_lt ??? ge0)) (n2 Hn2); clear H2;
letin N ≝ (S (n2 + n1));
cases (Hn1 N ?) (H1 H2); [apply (ltwr ? n2); rewrite < sym_plus; apply le_n;]
cases (Hn2 N ?) (H3 H4); [apply (ltwl ? n1); rewrite < sym_plus; apply le_n;]
clear H1 H3 Hn2 Hn1 N ge0 Axy; lapply (mtineq ?? x y (xn (S (n2+n1)))) as H5;
cut ( δx (xn (S (n2+n1)))+ δ(xn (S (n2+n1))) y <   δx y/1 + δ(xn (S (n2+n1))) y) as H6;[2:
  apply flt_plusr; apply (Lt≪ ? (msymmetric ????)); assumption]
lapply (le_lt_transitive ???? H5 H6) as H7; clear H6;
cut (δx y/1+ δ(xn (S (n2+n1))) y < δx y/1+  δx y/1) as H6; [2:apply flt_plusl; assumption]
lapply (lt_transitive ???? H7 H6) as ABS; clear H6 H7 H4 H5 H2 n1 n2 xn;
lapply (divpow ? (δ x y) 1) as D; lapply (Lt≪ ? (eq_sym ??? D) ABS) as H;
change in H with ( δx y/1+ δx y/1< δx y/1+ δx y/1);
apply (lt_coreflexive ?? H);
qed.

(* 3.18 *)
