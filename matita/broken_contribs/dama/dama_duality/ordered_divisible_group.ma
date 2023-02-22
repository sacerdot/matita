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
include "nat/times.ma".
include "ordered_group.ma".
include "divisible_group.ma".

record todgroup : Type ≝ {
  todg_order:> togroup;
  todg_division_: dgroup;
  todg_with_: dg_carr todg_division_ = og_abelian_group todg_order
}.

lemma todg_division: todgroup → dgroup.
intro G; apply (mk_dgroup G); unfold abelian_group_OF_todgroup; 
cases (todg_with_ G); exact (dg_prop (todg_division_ G));
qed.

coercion cic:/matita/ordered_divisible_group/todg_division.con.

lemma mul_ge: ∀G:todgroup.∀x:G.∀n.0 ≤ x → 0 ≤ n * x.
intros (G x n); elim n; simplify; [apply le_reflexive]
apply (le_transitive ???? H1); 
apply (Le≪ (0+(n1*x)) (zero_neutral ??));
apply fle_plusr; assumption;
qed. 

lemma lt_ltmul: ∀G:todgroup.∀x,y:G.∀n. x < y → S n * x < S n * y.
intros; elim n; [simplify; apply flt_plusr; assumption]
simplify; apply (ltplus); [assumption] assumption;
qed.

lemma ltmul_lt: ∀G:todgroup.∀x,y:G.∀n. S n * x < S n * y → x < y.
intros 4; elim n; [apply (plus_cancr_lt ??? 0); assumption]
simplify in l; cases (ltplus_orlt ????? l); [assumption]
apply f; assumption;
qed.

lemma divide_preserves_lt: ∀G:todgroup.∀e:G.∀n.0<e → 0 < e/n.
intros; elim n; [apply (Lt≫ ? (div1 ??));assumption]
unfold divide; elim (dg_prop G e (S n1)); simplify; simplify in f;
apply (ltmul_lt ??? (S n1)); simplify; apply (Lt≫ ? p);
apply (Lt≪ ? (zero_neutral ??)); (* bug se faccio repeat *)
apply (Lt≪ ? (zero_neutral ??));  
apply (Lt≪ ? (mulzero ?n1));
assumption;
qed.

lemma muleqplus_lt: ∀G:todgroup.∀x,y:G.∀n,m.
   0<x → 0<y → S n * x ≈ S (n + S m) * y → y < x.
intros (G x y n m H1 H2 H3); apply (ltmul_lt ??? n); apply (Lt≫ ? H3);
clear H3; elim m; [
  rewrite > sym_plus; simplify; apply (Lt≪ (0+(y+n*y))); [
    apply eq_sym; apply zero_neutral]
  apply flt_plusr; assumption;]
apply (lt_transitive ???? l); rewrite > sym_plus; simplify;  
rewrite > (sym_plus n); simplify; repeat apply flt_plusl;
apply (Lt≪ (0+(n1+n)*y)); [apply eq_sym; apply zero_neutral]
apply flt_plusr; assumption;
qed.  

