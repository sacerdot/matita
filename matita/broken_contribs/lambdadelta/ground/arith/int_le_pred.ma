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

include "ground/arith/int_pred_succ.ma".
include "ground/arith/int_le.ma".

(* ORDER FOR INTEGERS *******************************************************)

(* Advanced constructions ***************************************************)

lemma zle_pred_sn (z1) (z2):
      z1 ≤ z2 → ↓z1 ≤ z2.
#z1 #z2 #Hz elim Hz -z2
/2 width=1 by zle_succ_dx/
qed.

lemma zle_neg_zero (p):
      −p ≤ 𝟎.
#p elim p -p
/2 width=1 by zle_pred_sn/
qed.

lemma int_split_le_ge_zero (z):
      ∨∨ z ≤ 𝟎 | 𝟎 ≤ z.
* /2 width=1 by zle_refl, or_introl, or_intror/
qed.

(* Advanced destructions ****************************************************)

lemma zle_des_neg_dx (z) (q):
     z ≤ −q →
     ∃p. −p = z.
#z1 #q @insert_eq_1
#z2 #Hz generalize in match q; -q elim Hz -z2
[ /2 width=2 by ex_intro/
| #z2 #_ #IH #q #H0
  lapply (eq_inv_zneg_succ … H0) -H0 #H0 destruct
  elim IH -IH [|*: // ] #z2 #Hz destruct
  /2 width=2 by ex_intro/
]
qed-.

(* Advanced inversions ******************************************************)

lemma zle_inv_zero_neg (q):
      (𝟎) ≤ −q → ⊥.
#q #H0
elim (zle_des_neg_dx … H0) -H0 #p #H0 destruct
qed-.

(* Constructions with zpred *************************************************)

lemma zle_pred_bi (z1) (z2):
      z1 ≤ z2 → ↓z1 ≤ ↓z2.
#z1 #z2 #H0 elim H0 -z2
/2 width=1 by zle_succ_dx/
qed.

(* Inversions with zpred ****************************************************)

lemma zle_inv_pred_bi (z1) (z2):
      ↓z1 ≤ ↓z2 → z1 ≤ z2.
/2 width=1 by zle_succ_bi/
qed-.

(* Inversions with zsucc ****************************************************)

lemma zle_inv_succ_bi (z1) (z2):
      ↑z1 ≤ ↑z2 → z1 ≤ z2.
/2 width=1 by zle_pred_bi/
qed-.

lemma zle_inv_succ_self (z):
      ↑z ≤ z → ⊥.
@int_ind_steps
[ /3 width=1 by zle_inv_pred_bi/
| /2 width=2 by zle_inv_pos_zero/
| /3 width=1 by zle_inv_succ_bi/
qed-.

(* Main inversions **********************************************************)

theorem zle_antisym (z1) (z2):
        z1 ≤ z2 → z2 ≤ z1 → z1 = z2.
#z1 #z2 #H elim H -z2 //
#z2 #_ #IH #Hz
lapply (zle_des_succ_sn … Hz) #H0
lapply (IH H0) -IH -H0 #H0 destruct
elim (zle_inv_succ_self … Hz)
qed-.

(* Advanced eliminations ****************************************************)

lemma zle_des_succ_sn (z1) (z2):
      ↑z1 ≤ z2 → z1 ≤ z2.
/2 width=3 by zle_trans/
qed-.

lemma zle_inv_pred_sn (z1) (z2):
      ↓z1 ≤ z2 → z1 ≤ ↑z2.
/2 width=1 by zle_succ_bi/
qed-.

lemma zle_ind_steps (Q: relation2 …):
      (∀z1,z2. z1 ≤ z2 → Q z1 z2 → Q (↓z1) (↓z2)) →
      (∀z2. Q (𝟎) z2) →
      (∀z1,z2. z1 ≤ z2 → Q z1 z2 → Q (↑z1) (↑z2)) →
      ∀z1,z2. z1 ≤ z2 → Q z1 z2.
#Q #IH1 #IH2 #IH3
@int_ind_steps
[ #z1 #IH4 #z2 #Hz elim Hz -z2
  /5 width=1 by zle_inv_pred_sn, zle_succ_dx/
| /2 width=1 by/
| #z1 #IH4 #z2 #Hz elim Hz -z2
  /4 width=1 by zle_des_succ_sn/
]
qed-.
