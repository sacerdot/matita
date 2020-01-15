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

include "basic_2/rt_computation/csx_fpbq.ma".
include "basic_2/rt_computation/fpbs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with sn for unbound parallel rt-transition for terms **********)

(* Basic_2A1: was: csx_fpbs_conf *)
lemma fpbs_csx_conf: ∀h,G1,L1,T1. ❪G1,L1❫ ⊢ ⬈*𝐒[h] T1 →
                     ∀G2,L2,T2. ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫ → ❪G2,L2❫ ⊢ ⬈*𝐒[h] T2.
#h #G1 #L1 #T1 #HT1 #G2 #L2 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
/2 width=5 by csx_fpbq_conf/
qed-.
