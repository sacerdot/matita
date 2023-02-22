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



include "nat/times.ma".
include "nat/orders.ma".

include "decl.ma".

inductive L (T:Type):Type:=
  bottom: L T
 |j: T → L T.
 
inductive eq (T:Type) : L T → L T → Prop :=
 eq_refl:∀x:T. eq T (j ? x) (j ? x).

notation "hvbox(a break ≡ b)"
  non associative with precedence 45
for @{ 'equiv $a $b }.

interpretation "uguaglianza parziale" 'equiv x y = (eq ? x y).

coercion cic:/matita/tests/decl/L.ind#xpointer(1/1/2).
 
lemma sim: ∀T:Type. ∀x,y:T. (j ? x) ≡ (j ? y) → (j ? y) ≡ (j ? x).
 intros.
 inversion H.
 intros.
 apply eq_refl.
qed.

lemma trans: ∀T:Type. ∀x,y,z:T.
 (j ? x) ≡ (j ? y) → (j ? y) ≡ (j ? z) → (j ? x) ≡ (j ? z).
 intros.
 inversion H1.
 intros.
 rewrite > H2 in H.
 assumption.
qed.

axiom R:Type.
axiom R0:R.
axiom R1:R.
axiom Rplus: L R→L R→L R.
axiom Rmult: L R→L R→L R.(*
axiom Rdiv: L R→L R→L R.*)
axiom Rinv: L R→L R.
axiom Relev: L R→L R→L R.
axiom Rle: L R→L R→Prop.
axiom Rge: L R→L R→Prop.

interpretation "real plus" 'plus x y = (Rplus x y).

interpretation "real leq" 'leq x y = (Rle x y).

interpretation "real geq" 'geq x y = (Rge x y).

let rec elev (x:L R) (n:nat) on n: L R ≝
 match n with
  [O ⇒ match x with [bottom ⇒ bottom ? | j y ⇒ (j ? R1)]
  | S n ⇒ Rmult x (elev x n)
  ].

let rec real_of_nat (n:nat) : L R ≝
 match n with
  [ O ⇒ (j ? R0)
  | S n ⇒ real_of_nat n + (j ? R1)
  ].

coercion cic:/matita/tests/decl/real_of_nat.con.

axiom Rplus_commutative: ∀x,y:R. (j ? x) + (j ? y) ≡ (j ? y) + (j ? x).
axiom R0_neutral: ∀x:R. (j ? x) + (j ? R0) ≡ (j ? x).
axiom Rmult_commutative: ∀x,y:R. Rmult (j ? x) (j ? y) ≡ Rmult (j ? y) (j ? x).
axiom R1_neutral: ∀x:R. Rmult (j ? x) (j ? R1) ≡ (j ? x).

axiom Rinv_ok:
 ∀x:R. ¬((j ? x) ≡ (j ? R0)) → Rmult (Rinv (j ? x)) (j ? x) ≡ (j ? R1). 
definition is_defined :=
 λ T:Type. λ x:L T. ∃y:T. x = (j ? y).
axiom Rinv_ok2: ∀x:L R. ¬(x = bottom ?) → ¬(x ≡ (j ? R0)) → is_defined ? (Rinv x).

definition Rdiv :=
 λ x,y:L R. Rmult x (Rinv y).

(*
lemma pippo: ∀x:R. ¬((j ? x) ≡ (j ? R0)) → Rdiv (j ? R1) (j ? x) ≡ Rinv (j ? x).
 intros.
 unfold Rdiv.
 elim (Rinv_ok2 ? ? H).
 rewrite > H1.
 rewrite > Rmult_commutative.
 apply R1_neutral.
*)

axiom Rdiv_le: ∀x,y:R. (j ? R1) ≤ (j ? y) → Rdiv (j ? x) (j ? y) ≤ (j ? x).
axiom R2_1: (j ? R1) ≤ S (S O).


axiom Rdiv_pos: ∀ x,y:R.
 (j ? R0) ≤ (j ? x) → (j ? R1) ≤ (j ? y) → (j ? R0) ≤ Rdiv (j ? x) (j ? y).
axiom Rle_R0_R1: (j ? R0) ≤ (j ? R1).
axiom div: ∀x:R. (j ? x) = Rdiv (j ? x) (S (S O)) → (j ? x) = O.
