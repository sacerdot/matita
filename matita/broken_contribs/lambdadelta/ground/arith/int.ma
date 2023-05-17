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
include "ground/notation/functions/zero_0.ma".
include "ground/arith/pnat.ma".

(* INTEGERS *****************************************************************)

inductive int: Type[0] ≝
| zneg : ℤ⁺ → int
| zzero: int
| zpos : ℤ⁺ → int
.

coercion zpos.

interpretation
  "integers"
  'Integers = (int).

interpretation
  "zero (integers)"
  'Zero = (zzero).

(* Basic inversions *********************************************************)

(* Note: destruct *)
lemma eq_inv_zneg_zero (p): zneg p = 𝟎 → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zero_zneg (p): 𝟎 = zneg p → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zneg_bi: injective … zneg.
#p1 #p2 #H destruct //
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_zero (p): zpos p = 𝟎 → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zero_zpos (p): 𝟎 = zpos p → ⊥.
#p #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_bi: injective … zpos.
#p1 #p2 #H destruct //
qed-.

(* Note: destruct *)
lemma eq_inv_zneg_pos (p1) (p2): zneg p1 = zpos p2 → ⊥.
#p1 #p2 #H0 destruct
qed-.

(* Note: destruct *)
lemma eq_inv_zpos_neg (p1) (p2): zpos p1 = zneg p2 → ⊥.
#p1 #p2 #H0 destruct
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
