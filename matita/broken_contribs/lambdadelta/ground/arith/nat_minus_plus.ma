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

include "ground/arith/nat_plus.ma".
include "ground/arith/nat_minus.ma".

(* SUBTRACTION FOR NON-NEGATIVE INTEGERS ************************************)

(* Constructions with nplus *************************************************)

(*** minus_plus_m_m *)
lemma nminus_plus_sn_refl_sn (m) (n): m = m + n - n.
#m #n @(nat_ind_succ … n) -n //
#n #IH <nplus_succ_dx <nminus_succ_bi //
qed.

(*** minus_plus_m_m_commutative *)
lemma nminus_plus_sn_refl_dx (m) (n): m = n + m - n.
#m #n <nplus_comm //
qed.

(*** minus_plus *)
theorem nminus_plus_assoc (o) (m) (n): o-m-n = o-(m+n).
#o #m #n @(nat_ind_succ … n) -n //
#n #IH <nplus_succ_dx <nminus_succ_dx <nminus_succ_dx //
qed.

(*** minus_plus_plus_l *)
lemma nminus_plus_dx_bi (m) (n) (o): m - n = (m + o) - (n + o).
#m #n #o <nminus_plus_assoc <nminus_comm_21 //
qed.

(* Helper constructions with nplus ******************************************)

(*** plus_to_minus *)
lemma nminus_plus_dx (o) (m) (n): o = m+n → n = o-m.
#o #m #n #H destruct //
qed-.

lemma nminus_plus_sn (o) (m) (n): o = m+n → m = o-n.
#o #m #n #H destruct //
qed-.

(* Inversions with nplus ****************************************************)

(*** discr_plus_xy_minus_xz *)
lemma eq_inv_plus_nminus_refl_sn (m) (n) (o):
      m + o = m - n →
      ∨∨ ∧∧ 𝟎 = m & 𝟎 = o
       | ∧∧ 𝟎 = n & 𝟎 = o.
#m #n @(nat_ind_2_succ … m n) -m -n
[ /3 width=1 by or_introl, conj/
| #m #_ #o #Ho
  lapply (eq_inv_nplus_bi_sn … (𝟎) Ho) -Ho
  /3 width=1 by or_intror, conj/
| #m #n #IH #o
  <nminus_succ_bi >nplus_succ_shift #Ho
  elim (IH … Ho) -IH -Ho * #_ #H
  elim (eq_inv_zero_nsucc … H)
]
qed-.

(*** discr_minus_x_xy *)
lemma eq_inv_nminus_refl_sn (m) (n): m = m - n → ∨∨ 𝟎 = m | 𝟎 = n.
#m #n #Hmn
elim (eq_inv_plus_nminus_refl_sn … (𝟎) Hmn) -Hmn * #H1 #H2
/2 width=1 by or_introl, or_intror/
qed-.
