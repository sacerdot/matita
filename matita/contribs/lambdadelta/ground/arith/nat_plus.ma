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

include "ground/arith/nat_succ_iter.ma".

(* ADDITION FOR NON-NEGATIVE INTEGERS ***************************************)

(*** plus *)
definition nplus: nat → nat → nat ≝
           λm,n. nsucc^n m.

interpretation
  "plus (positive integers"
  'plus m n = (nplus m n).

(* Basic rewrites ***********************************************************)

(*** plus_n_O *)
lemma nplus_zero_dx (m): m = m + 𝟎.
// qed.

lemma nplus_one_dx (n): ↑n = n + 𝟏.
// qed.

(* Advanved rewrites (semigroup properties) *********************************)

(*** plus_n_Sm *)
lemma nplus_succ_dx (m) (n): ↑(m+n) = m + ↑n.
#m #n @(niter_succ … nsucc)
qed.

lemma nplus_succ_sn (m) (n): ↑(m+n) = ↑m + n.
#m #n @(niter_appl … nsucc)
qed.

(*** plus_O_n.con *)
lemma nplus_zero_sn (m): m = 𝟎 + m.
#m @(nat_ind … m) -m //
qed.

(*** commutative_plus *)
lemma nplus_comm: commutative … nplus.
#m @(nat_ind … m) -m //
qed-.

(*** associative_plus *)
lemma nplus_assoc: associative … nplus.
#m #n #o @(nat_ind … o) -o //
#o #IH <nplus_succ_dx <nplus_succ_dx <nplus_succ_dx <IH -IH //
qed.

(* Advanced constructions ***************************************************)

lemma nplus_one_sn (n): ↑n = 𝟏 + n.
#n <nplus_comm // qed.

lemma nplus_succ_shift (m) (n): ↑m + n = m + ↑n.
// qed-.

(*** assoc_plus1 *)
lemma nplus_plus_comm_12 (o) (m) (n): m + n + o = n + (m + o).
#o #m #n <nplus_comm in ⊢ (??(?%?)?); // qed.

(*** plus_plus_comm_23 *)
lemma nplus_plus_comm_23 (o) (m) (n): o + m + n = o + n + m.
#o #m #n >nplus_assoc >nplus_assoc <nplus_comm in ⊢ (??(??%)?); //
qed-.

(* Basic inversions *********************************************************)

lemma eq_inv_nzero_plus (m) (n): 𝟎 = m + n → ∧∧ 𝟎 = m & 𝟎 = n.
#m #n @(nat_ind … n) -n /2 width=1 by conj/
#n #_ <nplus_succ_dx #H
elim (eq_inv_nzero_succ … H)
qed-.

(*** injective_plus_l *)
lemma eq_inv_nplus_bi_dx (o) (m) (n): m + o = n + o → m = n.
#o @(nat_ind … o) -o /3 width=1 by eq_inv_nsucc_bi/
qed-.

(*** injective_plus_r *)
lemma eq_inv_nplus_bi_sn (o) (m) (n): o + m = o + n → m = n.
#o #m #n <nplus_comm <nplus_comm in ⊢ (???%→?);
/2 width=2 by eq_inv_nplus_bi_dx/
qed-.

(* Advanced eliminations ****************************************************)

(*** nat_ind_plus *)
lemma nat_ind_plus (Q:predicate …):
      Q (𝟎) → (∀n. Q n → Q (𝟏+n)) → ∀n. Q n.
#Q #IH1 #IH2 #n @(nat_ind … n) -n /2 width=1 by/
qed-.
