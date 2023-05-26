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

include "ground/xoa/or_3.ma".
include "ground/arith/pnat_le.ma".

(* STRICT ORDER FOR POSITIVE INTEGERS ***************************************)

definition plt: relation2 (ℕ⁺) (ℕ⁺) ≝
           λp,q. ↑p ≤ q.

interpretation
  "less (positive integers)"
  'lt p q = (plt p q).

(* Basic constructions ******************************************************)

lemma plt_i (p) (q): ↑p ≤ q → p < q.
// qed.

lemma plt_refl_succ (q): q < ↑q.
// qed.

lemma plt_succ_dx (p) (q): p ≤ q → p < ↑q.
/2 width=1 by ple_succ_bi/ qed.

lemma plt_succ_dx_trans (p) (q): p < q → p < ↑q.
/2 width=1 by ple_succ_dx/ qed.

lemma plt_unit_succ (p): 𝟏 < ↑p.
/2 width=1 by ple_succ_bi/ qed.

lemma plt_succ_bi (p) (q): p < q → ↑p < ↑q.
/2 width=1 by ple_succ_bi/ qed.

lemma ple_split_lt_eq (p) (q): p ≤ q → ∨∨ p < q | p = q.
#p #q * -q /3 width=1 by ple_succ_bi, or_introl/
qed-.

lemma pnat_split_unit_gt (q): ∨∨ 𝟏 = q | 𝟏 < q.
#q elim (ple_split_lt_eq (𝟏) q ?)
/2 width=1 by or_introl, or_intror/
qed-.

lemma pnat_split_lt_ge (p) (q): ∨∨ p < q | q ≤ p.
#p #q elim (pnat_split_le_ge p q) /2 width=1 by or_intror/
#H elim (ple_split_lt_eq … H) -H /2 width=1 by ple_refl, or_introl, or_intror/
qed-.

lemma pnat_split_lt_eq_gt (p) (q): ∨∨ p < q | q = p | q < p.
#p #q elim (pnat_split_lt_ge p q) /2 width=1 by or3_intro0/
#H elim (ple_split_lt_eq … H) -H /2 width=1 by or3_intro1, or3_intro2/
qed-.

lemma le_false_plt (p) (q): (q ≤ p → ⊥) → p < q.
#p #q elim (pnat_split_lt_ge p q) [ // ]
#H #Hq elim Hq -Hq // 
qed.

lemma plt_ple_trans (r) (p) (q): p < r → r ≤ q → p < q.
/2 width=3 by ple_trans/ qed-.

lemma ple_plt_trans (r) (p) (q): p ≤ r → r < q → p < q.
/3 width=3 by ple_succ_bi, ple_trans/ qed-.

(* Basic inversions *********************************************************)

lemma plt_inv_succ_dx (p) (q): p < ↑q → p ≤ q.
/2 width=1 by ple_inv_succ_bi/ qed-.

lemma plt_inv_succ_bi (p) (q): ↑p < ↑q → p < q.
/2 width=1 by ple_inv_succ_bi/ qed-.

lemma plt_ge_false (p) (q): p < q → q ≤ p → ⊥.
/3 width=4 by ple_inv_succ_sn_refl, plt_ple_trans/ qed-.

lemma plt_inv_refl (p): p < p → ⊥.
/2 width=4 by plt_ge_false/ qed-.

lemma plt_inv_unit_dx (p): p < 𝟏 → ⊥.
/2 width=4 by plt_ge_false/ qed-.

(* Basic destructions *******************************************************)

lemma plt_des_le (p) (q): p < q → p ≤ q.
/2 width=3 by ple_trans/ qed-.

lemma plt_des_lt_unit_sn (p) (q): p < q → 𝟏 < q.
/3 width=3 by ple_plt_trans/ qed-.

(* Main constructions *******************************************************)

theorem plt_trans: Transitive … plt.
/3 width=3 by plt_des_le, plt_ple_trans/ qed-.

(* Advanced eliminations ****************************************************)

lemma pnat_ind_lt_le (Q:predicate …):
      (∀q. (∀p. p < q → Q p) → Q q) → ∀q,p. p ≤ q → Q p.
#Q #H1 #q elim q -q
[ #p #H <(ple_inv_unit_dx … H) -p
  @H1 -H1 #r #H elim (plt_inv_unit_dx … H)
| /5 width=3 by plt_ple_trans, ple_inv_succ_bi/
]
qed-.

lemma pnat_ind_lt (Q:predicate …):
      (∀q. (∀p. p < q → Q p) → Q q) → ∀q. Q q.
/4 width=2 by pnat_ind_lt_le/ qed-.

lemma plt_ind_alt (Q: relation2 …):
      (∀q. Q (𝟏) (↑q)) →
      (∀p,q. p < q → Q p q → Q (↑p) (↑q)) →
      ∀p,q. p < q → Q p q.
#Q #IH1 #IH2 #p #q @(pnat_ind_2 … q p) -p -q //
[ #p #H
  elim (plt_inv_unit_dx … H)
| /4 width=1 by plt_inv_succ_bi/
]
qed-.

(* Advanced constructions (decidability) ************************************)

lemma dec_plt (R:predicate …):
      (∀q. Decidable … (R q)) →
      ∀q. Decidable … (∃∃p. p < q & R p).
#R #HR #q elim q -q [| #q * ]
[ @or_intror * /2 width=2 by plt_inv_unit_dx/
| * /4 width=3 by plt_succ_dx_trans, ex2_intro, or_introl/
| #H0 elim (HR q) -HR
  [ /3 width=3 by or_introl, ex2_intro/
  | #Hq @or_intror * #p #Hpq #Hp
    elim (ple_split_lt_eq … Hpq) -Hpq #H destruct [ -Hq | -H0 ]
    /4 width=3 by plt_inv_succ_bi, ex2_intro/
  ]
]
qed-.
