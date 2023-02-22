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

include "ground/arith/pnat_two.ma".
include "ground/arith/nat_le_minus_plus.ma".
include "ground/arith/nat_lt.ma".

(* ARITHMETICAL PROPERTIES FOR λδ-2A ****************************************)

(* Equalities ***************************************************************)

lemma plus_n_2: ∀n. (n + 𝟐) = n + 𝟏 + 𝟏.
// qed.

lemma arith_b1: ∀a,b,c1. c1 ≤ b → a - c1 - (b - c1) = a - b.
#a #b #c1 #H >nminus_comm_21 <nminus_assoc_comm_23 //
qed-.

lemma arith_b2: ∀a,b,c1,c2. c1 + c2 ≤ b → a - c1 - c2 - (b - c1 - c2) = a - b.
#a #b #c1 #c2 #H
>(nminus_plus_assoc ? c1 c2) >(nminus_plus_assoc ? c1 c2)
/2 width=1 by arith_b1/
qed-.

lemma arith_c1x: ∀x,a,b,c1. x + c1 + a - (b + c1) = x + a - b.
#x #a #b #c1
<nplus_plus_comm_23 //
qed.

lemma arith_h1: ∀a1,a2,b,c1. c1 ≤ a1 → c1 ≤ b →
                a1 - c1 + a2 - (b - c1) = a1 + a2 - b.
#a1 #a2 #b #c1 #H1 #H2
>nminus_plus_comm_23
/2 width=1 by arith_b1/
qed-.

lemma arith_i: ∀x,y,z. y < x → x+z-y-(𝟏) = x-y-(𝟏)+z.
/2 width=1 by nminus_plus_comm_23/ qed-.

(* Constructions ************************************************************)

fact le_repl_sn_conf_aux: ∀x,y,z:nat. x ≤ z → x = y → y ≤ z.
// qed-.

fact le_repl_sn_trans_aux: ∀x,y,z:nat. x ≤ z → y = x → y ≤ z.
// qed-.

lemma monotonic_le_minus_l2: ∀x1,x2,y,z. x1 ≤ x2 → x1 - y - z ≤ x2 - y - z.
/3 width=1 by nle_minus_bi_dx/ qed.

lemma arith_j: ∀x,y,z. x-y-(𝟏) ≤ x-(y-z)-𝟏.
/3 width=1 by nle_minus_bi_dx, nle_minus_bi_sn/ qed.

lemma arith_k_sn: ∀z,x,y,n. z < x → x+n ≤ y → x-z-(𝟏)+n ≤ y-z-𝟏.
#z #x #y #n #Hzx #Hxny
>nminus_plus_comm_23 [2: /2 width=1 by nle_minus_bi_sn/ ]
>nminus_plus_comm_23 [2: /2 width=1 by nlt_des_le/ ]
/2 width=1 by monotonic_le_minus_l2/
qed.

lemma arith_k_dx: ∀z,x,y,n. z < x → y ≤ x+n → y-z-(𝟏) ≤ x-z-(𝟏)+n.
#z #x #y #n #Hzx #Hyxn
>nminus_plus_comm_23 [2: /2 width=1 by nle_minus_bi_sn/ ]
>nminus_plus_comm_23 [2: /2 width=1 by nlt_des_le/ ]
/2 width=1 by monotonic_le_minus_l2/
qed.

(* Inversions ***************************************************************)

lemma lt_plus_SO_to_le: ∀x,y. x < y + (𝟏) → x ≤ y.
/2 width=1 by nle_inv_succ_bi/ qed-.

(* Iterators ****************************************************************)

lemma iter_SO: ∀B:Type[0]. ∀f:B→B. ∀b,l. (f^(l+𝟏)) b = f ((f^l) b).
#B #f #b #l
<niter_succ //
qed.
