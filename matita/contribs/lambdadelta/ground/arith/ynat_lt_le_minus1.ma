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
include "ground/arith/ynat_minus1.ma".
include "ground/arith/ynat_le.ma".
include "ground/arith/ynat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Cobstructions with yle and yminus1  **************************************)

(*** monotonic_ylt_minus_dx *)
lemma ylt_minus1_bi_dx (o) (x) (y):
      x < y → yinj_nat o ≤ x → x - o < y - o.
#o #x #y * -x -y
/4 width=1 by ylt_inj, yle_inv_inj_bi, nlt_minus_bi_dx/
qed.
