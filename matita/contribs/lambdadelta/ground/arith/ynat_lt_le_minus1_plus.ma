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

include "ground/arith/ynat_minus1_plus.ma".
include "ground/arith/ynat_lt_le_minus1.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yle and yminus1 and yplus  ****************************)

(*** ylt_plus2_to_minus_inj2 *)
lemma ylt_plus_dx_dx_minus1_sn (o) (x) (y):
      yinj_nat o ≤ x → x < y + yinj_nat o → x - o < y.
/2 width=1 by ylt_minus1_bi_dx/ qed.

(*** ylt_plus2_to_minus_inj1 *)
lemma ylt_plus_dx_sn_minus1_sn (o) (x) (y):
      yinj_nat o ≤ x → x < yinj_nat o + y → x - o < y.
/2 width=1 by ylt_plus_dx_dx_minus1_sn/ qed.
