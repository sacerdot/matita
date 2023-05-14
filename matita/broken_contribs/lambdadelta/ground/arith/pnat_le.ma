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

include "ground/generated/insert_eq_1.ma".
include "ground/arith/pnat.ma".

(* ORDER FOR POSITIVE INTEGERS **********************************************)

inductive ple (p:ℤ⁺): predicate (ℤ⁺) ≝
| ple_refl   : ple p p
| ple_succ_dx: ∀q. ple p q → ple p (↑q)
.

interpretation
  "less equal (positive integers)"
  'leq p q = (ple p q).

(* Basic constructions ******************************************************)

lemma ple_succ_dx_refl (p): p ≤ ↑p.
/2 width=1 by ple_refl, ple_succ_dx/ qed.

lemma ple_unit_sx (p): 𝟏 ≤ p.
#p elim p -p /2 width=1 by ple_succ_dx/
qed.

lemma ple_succ_bi (p) (q): p ≤ q → ↑p ≤ ↑q.
#p #q #H elim H -q /2 width=1 by ple_refl, ple_succ_dx/
qed.

lemma pnat_split_le_ge (p) (q): ∨∨ p ≤ q | q ≤ p.
#p #q @(pnat_ind_2 … p q) -p -q
[ /2 width=1 by or_introl/
| /2 width=1 by or_intror/
| #p #q * /3 width=2 by ple_succ_bi, or_introl, or_intror/
]
qed-.

(* Basic destructions *******************************************************)

lemma ple_des_succ_sn (p) (q): ↑p ≤ q → p ≤ q.
#p #q #H elim H -q /2 width=1 by ple_succ_dx/
qed-.

(* Basic inversions *********************************************************)

lemma ple_inv_succ_bi (p) (q): ↑p ≤ ↑q → p ≤ q.
#p #q @(insert_eq_1 … (↑q))
#x * -x
[ #H destruct //
| #o #Ho #H destruct
  /2 width=1 by ple_des_succ_sn/ 
]
qed-.

lemma ple_inv_unit_dx (p): p ≤ 𝟏 → 𝟏 = p.
#p @(insert_eq_1 … (𝟏))
#y * -y
[ #H destruct //
| #y #_ #H destruct
]
qed-.

(* Advanced inversions ******************************************************)

lemma ple_inv_succ_unit (p): ↑p ≤ 𝟏 → ⊥.
#p #H
lapply (ple_inv_unit_dx … H) -H #H destruct
qed-.

lemma ple_inv_succ_sn_refl (p): ↑p ≤ p → ⊥.
#p elim p -p [| #p #IH ] #H
[ /2 width=2 by ple_inv_succ_unit/
| /3 width=1 by ple_inv_succ_bi/
]
qed-.

theorem ple_antisym (p) (q): p ≤ q → q ≤ p → p = q.
#p #q #H elim H -q //
#q #_ #IH #Hq
lapply (ple_des_succ_sn … Hq) #H
lapply (IH H) -IH -H #H destruct
elim (ple_inv_succ_sn_refl … Hq)
qed-.

(* Advanced eliminations ****************************************************)

lemma ple_ind_alt (Q: relation2 …):
      (∀q. Q (𝟏) (q)) →
      (∀p,q. p ≤ q → Q p q → Q (↑p) (↑q)) →
      ∀p,q. p ≤ q → Q p q.
#Q #IH1 #IH2 #p #q @(pnat_ind_2 … p q) -p -q //
[ #p #_ #H elim (ple_inv_succ_unit … H)
| /4 width=1 by ple_inv_succ_bi/
]
qed-.

(* Advanced constructions ***************************************************)

theorem ple_trans: Transitive … ple.
#p #q #H elim H -q /3 width=1 by ple_des_succ_sn/
qed-.

lemma ple_dec (p) (q): Decidable … (p ≤ q).
#p #q elim (pnat_split_le_ge p q) [ /2 width=1 by or_introl/ ]
#Hqp elim (eq_pnat_dec p q) [ #H destruct /2 width=1 by ple_refl, or_introl/ ]
/4 width=1 by ple_antisym, or_intror/
qed-.
