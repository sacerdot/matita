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



include "nat/orders.ma".
include "group.ma".

let rec gpow (G : abelian_group) (x : G) (n : nat) on n : G ≝
  match n with [ O ⇒ 0 | S m ⇒ x + gpow ? x m].
  
interpretation "additive abelian group pow" 'times n x = (gpow ? x n).
  
record dgroup : Type ≝ {
  dg_carr:> abelian_group;
  dg_prop: ∀x:dg_carr.∀n:nat.∃y.S n * y ≈ x
}.

lemma divide: ∀G:dgroup.G → nat → G.
intros (G x n); cases (dg_prop G x n); apply w; 
qed.

interpretation "divisible group divide" 'divide x n = (divide ? x n).

lemma divide_divides: 
  ∀G:dgroup.∀x:G.∀n. S n * (x / n) ≈ x.
intro G; cases G; unfold divide; intros (x n); simplify;
cases (f x n); simplify; exact H;
qed.  
  
lemma feq_mul: ∀G:dgroup.∀x,y:G.∀n.x≈y → n * x ≈ n * y.
intros (G x y n H); elim n; [apply eq_reflexive]
simplify; apply (Eq≈ (x + (n1 * y)) H1);
apply (Eq≈ (y+n1*y) H (eq_reflexive ??));
qed.

lemma div1: ∀G:dgroup.∀x:G.x/O ≈ x.
intro G; cases G; unfold divide; intros; simplify;
cases (f x O); simplify; simplify in H; intro; apply H;
apply (Ap≪ ? (plus_comm ???));
apply (Ap≪ w (zero_neutral ??)); assumption;
qed.

lemma apmul_ap: ∀G:dgroup.∀x,y:G.∀n.S n * x # S n * y → x # y.
intros 4 (G x y n); elim n; [2:
  simplify in a;
  cases (applus ????? a); [assumption]
  apply f; assumption;]
apply (plus_cancr_ap ??? 0); assumption;
qed.

lemma plusmul: ∀G:dgroup.∀x,y:G.∀n.n * (x+y) ≈ n * x + n * y.
intros (G x y n); elim n; [
  simplify; apply (Eq≈ 0 ? (zero_neutral ? 0)); apply eq_reflexive]
simplify; apply eq_sym; apply (Eq≈ (x+y+(n1*x+n1*y))); [
  apply (Eq≈ (x+(n1*x+(y+(n1*y))))); [
    apply eq_sym; apply plus_assoc;]
  apply (Eq≈ (x+((n1*x+y+(n1*y))))); [
    apply feq_plusl; apply plus_assoc;]
  apply (Eq≈ (x+(y+n1*x+n1*y))); [
    apply feq_plusl; apply feq_plusr; apply plus_comm;] 
  apply (Eq≈ (x+(y+(n1*x+n1*y)))); [
    apply feq_plusl; apply eq_sym; apply plus_assoc;]
  apply plus_assoc;]
apply feq_plusl; apply eq_sym; assumption;
qed. 

lemma mulzero: ∀G:dgroup.∀n.n*0 ≈ 0. [2: apply dg_carr; apply G]
intros; elim n; [simplify; apply eq_reflexive]
simplify; apply (Eq≈ ? (zero_neutral ??)); assumption; 
qed.

let rec gpowS (G : abelian_group) (x : G) (n : nat) on n : G ≝
  match n with [ O ⇒ x | S m ⇒ gpowS ? x m + x].
  
lemma gpowS_gpow: ∀G:dgroup.∀e:G.∀n. S n * e ≈ gpowS ? e n.
intros (G e n); elim n; simplify; [
  apply (Eq≈ ? (plus_comm ???));apply zero_neutral]
apply (Eq≈ ?? (plus_comm ???));  
apply (Eq≈ (e+S n1*e) ? H); clear H; simplify; apply eq_reflexive;
qed.

lemma divpow: ∀G:dgroup.∀e:G.∀n. e ≈ gpowS ? (e/n) n.
intros (G e n); apply (Eq≈ ?? (gpowS_gpow ?(e/n) n));
apply eq_sym; apply divide_divides;
qed.
