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

include "ground/notation/functions/integers_0.ma".
include "ground/notation/functions/minus_1.ma".
include "ground/notation/functions/zero_0.ma".
include "ground/notation/functions/invisibleplus_1.ma".
include "ground/arith/pnat.ma".

(* INTEGERS *****************************************************************)

inductive int: Type[0] ≝
| zneg : ℕ⁺ → int
| zzero: int
| zpos : ℕ⁺ → int
.

interpretation
  "integers"
  'Integers = (int).

interpretation
  "negative projection (integers)"
  'Minus p = (zneg p).

interpretation
  "zero (integers)"
  'Zero = (zzero).

interpretation
  "positive projection (integers)"
  'InvisiblePlus p = (zpos p).

(* Basic inversions *********************************************************)

(* Note: destruct *)
lemma eq_inv_zneg_zero (p): −p = 𝟎 → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zzero_neg (p): 𝟎 = −p → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zneg_bi: injective … zneg.
#p1 #p2 #H destruct //
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_zero (p): ⁤p =❪ℤ❫ 𝟎 → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zzero_pos (p): 𝟎 =❪ℤ❫ ⁤p → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_bi: injective … zpos.
#p1 #p2 #H destruct //
qed-.

(* Note: destruct *)
lemma eq_inv_zneg_pos (p1) (p2): −p1 = ⁤p2 → ⊥.
#p1 #p2 #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_neg (p1) (p2): ⁤p1 = −p2 → ⊥.
#p1 #p2 #H0 destruct
qed-.

(* Basic eliminators ********************************************************)

lemma int_ind_psucc (Q:predicate …):
      (∀p. Q (−p) → Q (−↑p)) →
      Q (−𝟏) →
      Q (𝟎) →
      Q (⁤𝟏) →
      (∀p. Q (⁤p) → Q (⁤↑p)) →
      ∀z. Q z.
#Q #IH1 #IH2 #IH3 #IH4 #IH5
* // #p elim p -p // #p #IH
/2 width=1 by/
qed-.

(* Basic constructions ******************************************************)

lemma eq_int_dec (z1,z2:ℤ): Decidable (z1 = z2).
* [2: |*: #p1 ] * [2,5,8: |*: #p2 ]
[1: /2 width=1 by or_introl/
|6: elim (eq_pnat_dec p1 p2)
    /4 width=1 by eq_inv_zneg_bi, or_intror, or_introl/
|9: elim (eq_pnat_dec p1 p2)
    /4 width=1 by eq_inv_zpos_bi, or_intror, or_introl/
|*: @or_intror #H destruct
]
qed-.
