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

include "ground/arith/ynat_le_plus.ma".
include "ground/arith/ynat_lt_plus.ma".
include "ground/arith/ynat_lt_le.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY *********************)

(* Constructions with yle and yplus *****************************************)

(*** monotonic_ylt_plus_inj *)
lemma ylt_yle_plus_bi_inj (x1) (x2) (n1) (y2):
      x1 < x2 → yinj_nat n1 ≤ y2 → x1 + yinj_nat n1 < x2 + y2.
/3 width=3 by ylt_plus_bi_dx_inj, yle_plus_bi_sx, ylt_yle_trans/
qed.

(*** monotonic_ylt_plus *)
lemma ylt_yle_plus_bi (x1) (x2) (y1) (y2):
      x1 < x2 → y1 < ∞ → y1 ≤ y2 → x1 + y1 < x2 + y2.
#x1 #x2 #y1 #y2 #Hx12 #Hy1 #Hy12
elim (ylt_des_gen_sx … Hy1) -Hy1 #n1 #H destruct
/2 width=1 by ylt_yle_plus_bi_inj/
qed.

(* Inversions with yle and yplus ********************************************)

(*** yle_inv_monotonic_plus_dx *)
lemma yle_inv_plus_bi_dx (z) (x) (y):
      z < ∞ → x + z ≤ y + z → x ≤ y.
#z #x #y #Hz #Hxy
elim (ylt_des_gen_sx … Hz) -Hz #o #H destruct
/2 width=2 by yle_inv_plus_bi_sx_inj/
qed-.

(*** yle_inv_monotonic_plus_sx *)
lemma yle_inv_plus_bi_sx (z) (x) (y):
      z < ∞ → z + x ≤ z + y → x ≤ y.
/2 width=3 by yle_inv_plus_bi_dx/ qed-.

(* Destructions with yle and yplus ******************************************)

(*** ylt_fwd_plus_ge *)
lemma ylt_des_plus_bi_sx_ge (x1) (x2) (y1) (y2):
      x2 ≤ x1 → x1 + y1 < x2 + y2 → y1 < y2.
#x1 #x2 #y1 #y2 #Hx21 #Hxy
elim (ylt_des_gen_sx … Hxy) #o #H
elim (eq_inv_yplus_inj … H) -H #m1 #n1 #_ #H2 #H3 destruct -o
elim (yle_inv_inj_dx … Hx21) #m2 #_ #H destruct
lapply (ylt_yle_plus_bi_inj … Hxy … Hx21) -Hxy -Hx21
<yplus_plus_comm_13 #H
/3 width=3 by ylt_des_plus_bi_sx, ylt_des_plus_bi_dx/
qed-.
