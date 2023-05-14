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

include "ground/arith/nat_lt_minus.ma".
include "ground/arith/ynat_lminus.ma".
include "ground/arith/ynat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ylminus ***********************************************)

(*** ylt_to_minus *)
lemma ylt_zero_lminus (m) (y):
      yinj_nat m < y → 𝟎 < y - m.
#m #y @(ynat_split_nat_inf … y) -y //
#n #Hmn <ylminus_inj_sn >yinj_nat_zero >(nminus_refl m)
/4 width=1 by ylt_inj, ylt_inv_inj_bi, nlt_minus_bi_dx/
qed.

(* Inversions with ylminus **************************************************)

(*** yminus_to_lt *)
lemma ylt_inv_zero_lminus (m) (y):
      (𝟎) < y - m → yinj_nat m < y.
#m #y @(ynat_split_nat_inf … y) -y //
#n <ylminus_inj_sn >yinj_nat_zero >(nminus_refl m) #Hmm
/4 width=2 by ylt_inv_inj_bi, ylt_inj, nlt_inv_minus_bi_dx/
qed-.

(* Destructions with ylminus ************************************************)

(*** yminus_pred *)
lemma ylminus_pred_bi (x:ynat) (n):
      (𝟎) < x → 𝟎 < n → x - n = ⫰x - ⫰n.
#x @(ynat_split_nat_inf … x) -x //
#m #n >yinj_nat_zero
#Hm #Hn <ylminus_inj_sn <ypred_inj <ylminus_inj_sn
<nminus_pred_bi /2 width=1 by ylt_inv_inj_bi/
qed-.
