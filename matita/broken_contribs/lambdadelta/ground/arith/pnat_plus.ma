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

include "ground/arith/pnat_iter.ma".

(* ADDITION FOR POSITIVE INTEGERS *******************************************)

definition pplus: ℕ⁺ → ℕ⁺ → ℕ⁺ ≝
           λp,q. (psucc^q) p.

interpretation
  "plus (positive integers)"
  'plus p q = (pplus p q).

(* Basic constructions ******************************************************)

lemma pplus_unit_dx (p): ↑p = p + 𝟏.
// qed.

lemma pplus_succ_dx (p) (q): ↑(p+q) = p + ↑q.
// qed.

(* Advanced constructions (semigroup properties) ****************************)

lemma pplus_succ_sn (p) (q): ↑(p+q) = ↑p + q.
#p #q @(piter_appl … psucc)
qed.

lemma pplus_unit_sn (p): ↑p = 𝟏 + p.
#p elim p -p //
qed.

lemma pplus_comm: commutative … pplus.
#p elim p -p //
qed-. (* * gets in the way with auto *)

lemma pplus_assoc: associative … pplus.
#p #q #r elim r -r //
#r #IH <pplus_succ_dx <pplus_succ_dx <IH -IH //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_unit_pplus (p) (q): 𝟏 = p + q → ⊥.
#p #q elim q -q
[ <pplus_unit_dx #H destruct
| #q #_ <pplus_succ_dx #H destruct
]
qed-.

lemma eq_inv_pplus_unit (p) (q):
      p + q = 𝟏 → ⊥.
/2 width=3 by eq_inv_unit_pplus/ qed-.

lemma eq_inv_pplus_bi_dx (r) (p) (q): p + r = q + r → p = q.
#r elim r -r /3 width=1 by eq_inv_psucc_bi/
qed-.

lemma eq_inv_pplus_bi_sn (r) (p) (q): r + p = r + q → p = q.
#r #p #q <pplus_comm <pplus_comm in ⊢ (???%→?);
/2 width=2 by eq_inv_pplus_bi_dx/
qed-.
