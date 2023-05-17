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

include "ground/arith/nat_psucc.ma".

(* SUCCESSOR FOR NON-NEGATIVE INTEGERS **************************************)

(* Basic constructions ******************************************************)

lemma nsucc_inj (p): (↑p) ={ℕ} ↑(npos p).
// qed-.

(* Basic eliminations *******************************************************)

(*** nat_ind *)
lemma nat_ind_succ (Q:predicate …):
      Q (𝟎) → (∀n. Q n → Q (↑n)) → ∀n. Q n.
#Q #IH1 #IH2 * //
#p elim p -p /2 width=1 by/
qed-.

(*** nat_elim2 *)
lemma nat_ind_2_succ (Q:relation2 …):
      (∀n. Q (𝟎) n) →
      (∀m. Q m (𝟎) → Q (↑m) (𝟎)) →
      (∀m,n. Q m n → Q (↑m) (↑n)) →
      ∀m,n. Q m n.
#Q #IH1 #IH2 #IH3 #m @(nat_ind_succ … m) -m [ // ]
#m #IH #n @(nat_ind_succ … n) -n /2 width=1 by/
qed-.

(* Basic inversions *********************************************************)

(*** injective_S *)
lemma eq_inv_nsucc_bi (n1) (n2):
      ↑n1 ={ℕ} ↑n2 → n1 = n2.
/3 width=1 by eq_inv_npsucc_bi, eq_inv_npos_bi/
qed-.

(*** succ_inv_refl_sn *)
lemma nsucc_inv_refl (n:ℕ): n = ↑n → ⊥.
*
[ #H0 destruct
| #p #H0 /3 width=2 by eq_inv_npos_bi, psucc_inv_refl/
]
qed-.
