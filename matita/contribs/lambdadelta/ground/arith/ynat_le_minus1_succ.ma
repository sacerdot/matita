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

include "ground/arith/ynat_succ.ma".
include "ground/arith/ynat_le_minus1.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with yminus1 and ysucc *************************************)

(*** yminus_succ1_inj *)
lemma yminus1_succ_sn (x) (n):
      yinj_nat n ≤ x → ↑(x - n) = ↑x - n.
#x @(ynat_split_nat_inf … x) -x //
#m #n #Hnm
<yminus1_inj_sn <ysucc_inj <ysucc_inj <yminus1_inj_sn
/4 width=1 by yle_inv_inj_bi, nminus_succ_sn, eq_f/
qed-.
