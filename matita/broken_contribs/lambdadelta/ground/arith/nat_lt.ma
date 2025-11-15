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

include "ground/arith/pnat_lt.ma".
include "ground/arith/nat_succ.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Note: includes: plt_npsucc_bi *)
(*** lt *)
definition nlt: relation2 (ℕ) (ℕ) ≝
           λn1,n2. ↑n1 < ↑n2.

interpretation
  "less (non-negative integers)"
  'lt m n = (nlt m n).

(* Basic inversions *********************************************************)

(*** lt_S_S_to_lt *)
lemma nlt_inv_succ_bi (m) (n): (⁤↑m) < (⁤↑n) → m < n.
/2 width=1 by plt_inv_succ_bi/
qed-.

lemma nlt_inv_succ_dx (m) (n): m < (⁤↑n) → ∨∨ m = n | m < n.
#m #n #H0
lapply (plt_inv_succ_dx … H0) -H0 #H0
elim (ple_split_lt_eq … H0) -H0
[ /2 width=1 by or_intror/
| /3 width=1 by eq_inv_npsucc_bi, or_introl/
]
qed-.

(*** lt_to_not_eq lt_refl_false *)
lemma nlt_inv_refl (m): m < m → ⊥.
/2 width=4 by plt_inv_refl/
qed-.

(*** lt_zero_false *)
lemma nlt_inv_zero_dx (m): m < 𝟎 → ⊥.
/2 width=4 by plt_inv_unit_dx/
qed-.

lemma nlt_inv_zero_sx_pos (n):
      (𝟎) < n → ∃p. (⁤p) = n.
*
[ #H0 elim (nlt_inv_refl … H0)
| /2 width=2 by ex_intro/
]
qed-.

lemma nlt_inv_pos_bi (p1) (p2):
      (⁤p1) < (⁤p2) → p1 < p2.
/2 width=1 by plt_inv_succ_bi/
qed-.

(* Basic constructions ******************************************************)

lemma nlt_unfold (n1:ℕ) (n2:ℕ):
      (↑n1 < ↑n2) = (n1 < n2).
//
qed.

lemma nlt_refl_succ (n): n < (⁤↑n).
//
qed.

(*** lt_S *)
lemma nlt_succ_dx_trans (m) (n): m < n → m < (⁤↑n).
/2 width=1 by plt_succ_dx_trans/
qed.

(*** lt_O_S *)
lemma nlt_zero_succ (m): 𝟎 < (⁤↑m).
//
qed.

(*** lt_S_S *)
lemma nlt_succ_bi (m) (n): m < n → (⁤↑m) < (⁤↑n).
/2 width=1 by plt_succ_bi/
qed.

(*** eq_or_gt *)
lemma nat_split_zero_gt (n): ∨∨ 𝟎 = n | 𝟎 < n.
#n elim (pnat_split_unit_gt (↑n))
[ #H0 <(eq_inv_unit_npsucc … H0) -H0
  /2 width=1 by or_introl/
| /3 width=1 by nlt_inv_succ_bi, or_intror/
]
qed-.

(*** lt_or_eq_or_gt *)
lemma nat_split_lt_eq_gt (m) (n): ∨∨ m < n | n = m | n < m.
#m #n elim (pnat_split_lt_eq_gt (↑m) (↑n))
[ /3 width=1 by nlt_inv_succ_bi, or3_intro0/
| /3 width=1 by eq_inv_npsucc_bi, or3_intro1/
| /3 width=1 by nlt_inv_succ_bi, or3_intro2/
]
qed-.

lemma nlt_zero_pos (p):
      (𝟎) < (⁤p).
//
qed.

lemma nlt_pos_bi (p1) (p2):
      p1 < p2 → (⁤p1) < (⁤p2).
/2 width=1 by plt_succ_bi/
qed.

(* Basic destructions *******************************************************)

(*** ltn_to_ltO *)
lemma nlt_des_lt_zero_sx (m) (n): m < n → 𝟎 < n.
/3 width=2 by plt_des_lt_unit_sx, nlt_inv_succ_bi/
qed-.

(* Main constructions *******************************************************)

(*** transitive_lt *)
theorem nlt_trans: Transitive … nlt.
/2 width=3 by plt_trans/
qed-.

(* Advanced eliminations ****************************************************)

(*** nat_elim1 *)
lemma nat_ind_lt (Q:predicate …):
      (∀n. (∀m. m < n → Q m) → Q n) → ∀n. Q n.
#Q #IHQ *
[ @IHQ #m #H0 elim (nlt_inv_zero_dx … H0)
| #q @(pnat_ind_lt … q) -q #q #IH
  @IHQ *
  [ #_ @IHQ #m #H0 elim (nlt_inv_zero_dx … H0)
  | /3 width=1 by nlt_inv_pos_bi/
  ]
]
qed-.

(*** lt_elim *)
lemma nlt_ind_alt (Q: relation2 … (ℕ)):
      (∀n. Q (𝟎) (⁤↑n)) →
      (∀m,n. m < n → Q m n → Q (⁤↑m) (⁤↑n)) →
      ∀m,n. m < n → Q m n.
#Q #IH1 #IH2 #m #n @(nat_ind_2_succ … n m) -m -n //
[ #m #H
  elim (nlt_inv_zero_dx … H)
| /4 width=1 by nlt_inv_succ_bi/
]
qed-.

(* Advanced constructions (decidability) ************************************)

(*** dec_lt *)
lemma dec_nlt (R:predicate …):
      (∀n. Decidable … (R n)) →
      ∀n. Decidable … (∃∃m. m < n & R m).
#R #HR #n @(nat_ind_succ … n) -n [| #n * ]
[ @or_intror * /2 width=2 by nlt_inv_zero_dx/
| * /4 width=3 by nlt_succ_dx_trans, ex2_intro, or_introl/
| #H0 elim (HR n) -HR
  [ /3 width=3 by or_introl, ex2_intro/
  | #Hn @or_intror * #m #Hmn #Hm
    elim (nlt_inv_succ_dx … Hmn) -Hmn #H0 destruct
    /3 width=3 by ex2_intro/
  ]
]
qed-.
