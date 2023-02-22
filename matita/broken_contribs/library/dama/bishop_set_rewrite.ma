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

include "dama/bishop_set.ma".

coercion eq_sym.

lemma eq_trans:∀E:bishop_set.∀x,z,y:E.x ≈ y → y ≈ z → x ≈ z ≝ 
  λE,x,y,z.eq_trans_ E x z y.

notation > "'Eq'≈" non associative with precedence 55 
  for @{'eqrewrite}.
  
interpretation "eq_rew" 'eqrewrite = (eq_trans ? ? ?).

lemma le_rewl: ∀E:ordered_set.∀z,y,x:E. x ≈ y → x ≤ z → y ≤ z.
intros (E z y x Exy Lxz); apply (le_transitive ??? ? Lxz);
intro Xyz; apply Exy; right; assumption;
qed.

lemma le_rewr: ∀E:ordered_set.∀z,y,x:E. x ≈ y → z ≤ x → z ≤ y.
intros (E z y x Exy Lxz); apply (le_transitive ??? Lxz);
intro Xyz; apply Exy; left; assumption;
qed.

notation > "'Le'≪" non associative with precedence 55 for @{'lerewritel}.
interpretation "le_rewl" 'lerewritel = (le_rewl ? ? ?).
notation > "'Le'≫" non associative with precedence 55 for @{'lerewriter}.
interpretation "le_rewr" 'lerewriter = (le_rewr ? ? ?).

lemma ap_rewl: ∀A:bishop_set.∀x,z,y:A. x ≈ y → y # z → x # z.
intros (A x z y Exy Ayz); cases (bs_cotransitive ???x Ayz); [2:assumption]
cases (eq_sym ??? Exy H);
qed.
  
lemma ap_rewr: ∀A:bishop_set.∀x,z,y:A. x ≈ y → z # y → z # x.
intros (A x z y Exy Azy); apply bs_symmetric; apply (ap_rewl ???? Exy);
apply bs_symmetric; assumption;
qed.

notation > "'Ap'≪" non associative with precedence 55 for @{'aprewritel}.
interpretation "ap_rewl" 'aprewritel = (ap_rewl ? ? ?).
notation > "'Ap'≫" non associative with precedence 55 for @{'aprewriter}.
interpretation "ap_rewr" 'aprewriter = (ap_rewr ? ? ?).

lemma exc_rewl: ∀A:ordered_set.∀x,z,y:A. x ≈ y → y ≰ z → x ≰ z.
intros (A x z y Exy Ayz); cases (exc_cotransitive ?? x Ayz); [2:assumption]
cases Exy; right; assumption;
qed.
  
lemma exc_rewr: ∀A:ordered_set.∀x,z,y:A. x ≈ y → z ≰ y → z ≰ x.
intros (A x z y Exy Azy); cases (exc_cotransitive ??x Azy); [assumption]
cases (Exy); left; assumption;
qed.

notation > "'Ex'≪" non associative with precedence 55 for @{'ordered_setrewritel}.
interpretation "exc_rewl" 'ordered_setrewritel = (exc_rewl ? ? ?).
notation > "'Ex'≫" non associative with precedence 55 for @{'ordered_setrewriter}.
interpretation "exc_rewr" 'ordered_setrewriter = (exc_rewr ? ? ?).

(*
lemma lt_rewr: ∀A:ordered_set.∀x,z,y:A. x ≈ y → z < y → z < x.
intros (A x y z E H); split; cases H;
[apply (Le≫ ? (eq_sym ??? E));|apply (Ap≫ ? E)] assumption;
qed.

lemma lt_rewl: ∀A:ordered_set.∀x,z,y:A. x ≈ y → y < z → x < z.
intros (A x y z E H); split; cases H;
[apply (Le≪ ? (eq_sym ??? E));| apply (Ap≪ ? E);] assumption;
qed.

notation > "'Lt'≪" non associative with precedence 55 for @{'ltrewritel}.
interpretation "lt_rewl" 'ltrewritel = (lt_rewl ? ? ?).
notation > "'Lt'≫" non associative with precedence 55 for @{'ltrewriter}.
interpretation "lt_rewr" 'ltrewriter = (lt_rewr ? ? ?).
*)
