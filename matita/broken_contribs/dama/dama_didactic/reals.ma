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



include "nat/plus.ma".

axiom R:Type.
axiom R0:R.
axiom R1:R.
axiom Rplus: R→R→R.
axiom Ropp:R→R. (*funzione da x → -x*)
axiom Rmult: R→R→R.
axiom Rdiv: R→R→R.
axiom Relev: R→R→R.
axiom Rle: R→R→Prop.
axiom Rge: R→R→Prop.

interpretation "real plus" 'plus x y = (Rplus x y).

interpretation "real opp" 'uminus x = (Ropp x). 

notation "hvbox(a break · b)"
  right associative with precedence 60
for @{ 'mult $a $b }.

interpretation "real mult" 'mult x y = (Rmult x y).

interpretation "real leq" 'leq x y = (Rle x y).

interpretation "real geq" 'geq x y = (Rge x y).

let rec elev (x:R) (n:nat) on n: R ≝
 match n with
  [O ⇒ R1
  | S n ⇒ Rmult x (elev x n)
  ].

let rec real_of_nat (n:nat) : R ≝
 match n with
  [ O ⇒ R0
  | S n ⇒
     match n with
      [ O ⇒ R1
      | _ ⇒ real_of_nat n + R1
      ]
  ].

coercion cic:/matita/didactic/reals/real_of_nat.con.

axiom Rplus_commutative: ∀x,y:R. x+y = y+x.
axiom R0_neutral: ∀x:R. x+R0=x.
axiom Rdiv_le: ∀x,y:R. R1 ≤ y → Rdiv x y ≤ x.
axiom R2_1: R1 ≤ S (S O).
(* assioma falso! *)
axiom Rmult_Rle: ∀x,y,z,w. x ≤ y → z ≤ w → Rmult x z ≤ Rmult y w.

axiom Rdiv_pos: ∀ x,y:R. R0 ≤ x → R1 ≤ y → R0 ≤ Rdiv x y.
axiom Rle_R0_R1: R0 ≤ R1.
axiom div: ∀x:R. x = Rdiv x (S (S O)) → x = O.
(* Proprieta' elevamento a potenza NATURALE *)
axiom elev_incr: ∀x:R.∀n:nat. R1 ≤ x → elev x (S n) ≥ elev x n.
axiom elev_decr: ∀x:R.∀n:nat. R0 ≤ x ∧ x ≤ R1 → elev x (S n) ≤ elev x n.
axiom Rle_to_Rge: ∀x,y:R. x ≤ y → y ≥ x.
axiom Rge_to_Rle: ∀x,y:R. x ≥ y → y ≤ x.

(* Proprieta' elevamento a potenza TRA REALI *)
(*
axiom Relev_ge: ∀x,y:R.
 (x ≥ R1 ∧ y ≥ R1) ∨ (x ≤ R1 ∧ y ≤ R1) → Relev x y ≥ x.
axiom Relev_le: ∀x,y:R.
 (x ≥ R1 ∧ y ≤ R1) ∨ (x ≤ R1 ∧ y ≥ R1) → Relev x y ≤ x.
*)

lemma stupido: ∀x:R.R0+x=x.
 assume x:R.
 conclude (R0+x) = (x+R0).
                 = x
 done.
qed.

axiom opposto1: ∀x:R. x + -x = R0.
axiom opposto2: ∀x:R. -x = Rmult x (-R1).
axiom meno_piu: Rmult (-R1) (-R1) = R1.
axiom R1_neutral: ∀x:R.Rmult R1 x = x.
(* assioma falso *)
axiom uffa: ∀x,y:R. R1 ≤ x → y ≤ x · y. 
