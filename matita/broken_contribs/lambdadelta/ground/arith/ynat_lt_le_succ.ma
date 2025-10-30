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

include "ground/arith/ynat_lt_succ.ma".
include "ground/arith/ynat_lt_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with ysucc *************************************************)

(*** yle_lt yle_succ1_inj *)
lemma ylt_le_succ_sx (x) (y):
      x < ∞ → ⫯x ≤ y → x < y.
/3 width=3 by ylt_yle_trans, ylt_succ_dx_refl/ qed.

(* Inversions with yle and ysucc ********************************************)

(*** ylt_inv_le *)
lemma ylt_inv_le_succ_sx (x) (y):
      x < y → ∧∧ x < ∞ & ⫯x ≤ y.
#x #y * -x -y
/3 width=1 by yle_inj, conj/
qed-.

(* Destructions with yle and ysucc ******************************************)

(*** ylt_fwd_le_succ1 *)
lemma ylt_des_le_succ_sx (x) (y): x < y → ⫯x ≤ y.
#x #y #H
elim (ylt_inv_le_succ_sx … H) -H #_ //
qed-.

(*** ylt_fwd_succ2 *)
lemma ylt_des_succ_dx (x) (y): x < ⫯y → x ≤ y.
#x #y @(ynat_split_nat_inf … y) -y //
#n <ysucc_inj #H
elim (ylt_inv_inj_dx … H) -H #m #Hm #H destruct
/3 width=1 by yle_inj, nlt_inv_succ_dx/
qed-.
