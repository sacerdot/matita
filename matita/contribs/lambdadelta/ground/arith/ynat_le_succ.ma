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
include "ground/arith/ynat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS WITH INFINITY ****************************)

(* Constructions with ysucc *************************************************)

(*** yle_succ *)
lemma yle_succ_bi (x) (y): x ≤ y → ↑x ≤ ↑y.
#x #y * -x -y
/3 width=1 by yle_inj, yle_inf, nle_succ_bi/
qed.

(*** yle_succ_dx *)
lemma yle_succ_dx (x) (y): x ≤ y → x ≤ ↑y.
#x #y * -x -y
/3 width=1 by yle_inj, yle_inf, nle_succ_dx/
qed.

(*** yle_refl_S_dx *)
lemma yle_succ_dx_refl (x): x ≤ ↑x.
/2 width=1 by yle_succ_dx/ qed.

(* Inversions with ysucc ****************************************************)

(*** yle_inv_succ *)
lemma yle_inv_succ_bi (x) (y): ↑x ≤ ↑y → x ≤ y.
#x #y @(ynat_split_nat_inf … y) -y //
#n <ysucc_inj #H
elim (yle_inv_inj_dx … H) -H #o #Hmn #H
elim (eq_inv_ysucc_inj … H) -H #m #H1 #H2 destruct
/3 width=1 by yle_inj, nle_inv_succ_bi/
qed-.
