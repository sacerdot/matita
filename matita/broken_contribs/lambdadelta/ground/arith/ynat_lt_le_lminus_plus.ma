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

include "ground/arith/ynat_lminus_plus.ma".
include "ground/arith/ynat_lt_le_lminus.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yle and ylminus and yplus *****************************)

(*** ylt_plus2_to_minus_inj2 *)
lemma ylt_plus_dx_dx_lminus_sx (o) (x) (y):
      yinj_nat o ≤ x → x < y + yinj_nat o → x - o < y.
/2 width=1 by ylt_lminus_bi_dx/ qed.

(*** ylt_plus2_to_minus_inj1 *)
lemma ylt_plus_dx_sx_lminus_sx (o) (x) (y):
      yinj_nat o ≤ x → x < yinj_nat o + y → x - o < y.
/2 width=1 by ylt_plus_dx_dx_lminus_sx/ qed.
