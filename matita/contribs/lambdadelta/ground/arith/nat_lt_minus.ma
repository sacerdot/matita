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

include "ground/arith/nat_le_minus.ma".
include "ground/arith/nat_lt_pred.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Rewrites with nminus *****************************************************)

(*** minus_pred_pred *)
lemma nminus_pred_bi (m) (n): 𝟎 < m → 𝟎 < n → n - m = ↓n - ↓m.
#m #n #Hm #Hn
>(nlt_inv_zero_sn … Hm) in ⊢ (??%?); -Hm
>(nlt_inv_zero_sn … Hn) in ⊢ (??%?); -Hn
//
qed-.

(* Constructions with nminus ************************************************)

(*** monotonic_lt_minus_l *)
lemma nlt_minus_sn_bi (o) (m) (n): o ≤ m → m < n → m - o < n - o.
#o #m #n #Hom #Hmn
lapply (nle_minus_sn_bi … o Hmn) -Hmn
<(nminus_succ_sn … Hom) //
qed.
