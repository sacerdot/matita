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

include "ground_2/lib/arith.ma".

(* ARITHMETICAL PROPERTIES FOR λδ-2B ****************************************)

(* Equalities ***************************************************************)

lemma plus_n_2: ∀n. n + 2 = n + 1 + 1.
// qed.

lemma arith_b1: ∀a,b,c1. c1 ≤ b → a - c1 - (b - c1) = a - b.
#a #b #c1 #H >minus_minus_comm >minus_le_minus_minus_comm //
qed-.

lemma arith_b2: ∀a,b,c1,c2. c1 + c2 ≤ b → a - c1 - c2 - (b - c1 - c2) = a - b.
#a #b #c1 #c2 #H >minus_plus >minus_plus >minus_plus /2 width=1 by arith_b1/
qed-.

lemma arith_c1x: ∀x,a,b,c1. x + c1 + a - (b + c1) = x + a - b.
/3 by monotonic_le_minus_l, le_to_le_to_eq, le_n/ qed.

lemma arith_h1: ∀a1,a2,b,c1. c1 ≤ a1 → c1 ≤ b →
                a1 - c1 + a2 - (b - c1) = a1 + a2 - b.
#a1 #a2 #b #c1 #H1 #H2 >plus_minus /2 width=1 by arith_b2/
qed-.

lemma arith_i: ∀x,y,z. y < x → x+z-y-1 = x-y-1+z.
/2 width=1 by plus_minus/ qed-.

(* Properties ***************************************************************)

fact le_repl_sn_conf_aux: ∀x,y,z:nat. x ≤ z → x = y → y ≤ z.
// qed-.

fact le_repl_sn_trans_aux: ∀x,y,z:nat. x ≤ z → y = x → y ≤ z.
// qed-.

lemma arith_j: ∀x,y,z. x-y-1 ≤ x-(y-z)-1.
/3 width=1 by monotonic_le_minus_l, monotonic_le_minus_r/ qed.

lemma arith_k_sn: ∀z,x,y,n. z < x → x+n ≤ y → x-z-1+n ≤ y-z-1.
#z #x #y #n #Hzx #Hxny
>plus_minus [2: /2 width=1 by monotonic_le_minus_r/ ]
>plus_minus [2: /2 width=1 by lt_to_le/ ]
/2 width=1 by monotonic_le_minus_l2/
qed.

lemma arith_k_dx: ∀z,x,y,n. z < x → y ≤ x+n → y-z-1 ≤ x-z-1+n.
#z #x #y #n #Hzx #Hyxn
>plus_minus [2: /2 width=1 by monotonic_le_minus_r/ ]
>plus_minus [2: /2 width=1 by lt_to_le/ ]
/2 width=1 by monotonic_le_minus_l2/
qed.

(* Inversion & forward lemmas ***********************************************)

lemma lt_plus_SO_to_le: ∀x,y. x < y + 1 → x ≤ y.
/2 width=1 by monotonic_pred/ qed-.

(* Iterators ****************************************************************)

lemma iter_SO: ∀B:Type[0]. ∀f:B→B. ∀b,l. f^(l+1) b = f (f^l b).
#B #f #b #l >commutative_plus //
qed.
