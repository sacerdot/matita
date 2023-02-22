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



include "group.ma".

record is_ring (G:abelian_group) (mult:G→G→G) (one:G) : Prop
≝
 {  (* multiplicative monoid properties *)
    mult_assoc_: associative ? mult;
    one_neutral_left_: left_neutral ? mult one;
    one_neutral_right_: right_neutral ? mult one;
    (* ring properties *)
    mult_plus_distr_left_: distributive_left ? mult (plus G);
    mult_plus_distr_right_: distributive_right ? mult (plus G);
    not_eq_zero_one_: (0 ≠ one)
 }.
 
record ring : Type \def
 { r_abelian_group:> abelian_group;
   mult: r_abelian_group → r_abelian_group → r_abelian_group;
   one: r_abelian_group;
   r_ring_properties: is_ring r_abelian_group mult one
 }.

theorem mult_assoc: ∀R:ring.associative ? (mult R).
 intros;
 apply (mult_assoc_ ? ? ? (r_ring_properties R)).
qed.

theorem one_neutral_left: ∀R:ring.left_neutral ? (mult R) (one R).
 intros;
 apply (one_neutral_left_ ? ? ? (r_ring_properties R)).
qed.

theorem one_neutral_right: ∀R:ring.right_neutral ? (mult R) (one R).
 intros;
 apply (one_neutral_right_ ? ? ? (r_ring_properties R)).
qed.

theorem mult_plus_distr_left: ∀R:ring.distributive_left ? (mult R) (plus R).
 intros;
 apply (mult_plus_distr_left_ ? ? ? (r_ring_properties R)).
qed.

theorem mult_plus_distr_right: ∀R:ring.distributive_right ? (mult R) (plus R).
 intros;
 apply (mult_plus_distr_right_ ? ? ? (r_ring_properties R)).
qed.

theorem not_eq_zero_one: ∀R:ring.0 ≠ one R.
 intros;
 apply (not_eq_zero_one_ ? ? ? (r_ring_properties R)).
qed.

interpretation "Ring mult" 'times a b = (mult ? a b).

notation "1" with precedence 89
for @{ 'one }.

interpretation "Ring one" 'one = (one ?).

lemma eq_mult_zero_x_zero: ∀R:ring.∀x:R.0*x=0.
 intros;
 generalize in match (zero_neutral R 0); intro;
 generalize in match (eq_f ? ? (λy.y*x) ? ? H); intro; clear H;
 rewrite > mult_plus_distr_right in H1;
 generalize in match (eq_f ? ? (λy.-(0*x)+y) ? ? H1); intro; clear H1;
 rewrite < plus_assoc in H;
 rewrite > opp_inverse in H;
 rewrite > zero_neutral in H;
 assumption.
qed.

lemma eq_mult_x_zero_zero: ∀R:ring.∀x:R.x*0=0.
intros;
generalize in match (zero_neutral R 0);
intro;
generalize in match (eq_f ? ? (λy.x*y) ? ? H); intro; clear H;
(*CSC: qua funzionava prima della patch all'unificazione!*)
rewrite > (mult_plus_distr_left R) in H1;
generalize in match (eq_f ? ? (λy. (-(x*0)) +y) ? ? H1);intro;
clear H1;
rewrite < plus_assoc in H;
rewrite > opp_inverse in H;
rewrite > zero_neutral in H;
assumption.
qed.

