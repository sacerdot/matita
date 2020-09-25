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

include "static_2/s_computation/fqus_fqup.ma".
include "basic_2/rt_transition/fpbc_fqup.ma".
include "basic_2/rt_computation/fpbs_fqus.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/fpbg_fpbs.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Properties with plus-iterated structural successor for closures **********)

(* Note: this is used in the closure proof *)
lemma fqup_fpbg:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂+ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqup_inv_step_sn … H) -H
/3 width=5 by fpbc_fpbs_fpbg, fqus_fpbs, fqu_fpbc/
qed.

(* Note: this is used in the closure proof *)
lemma fqup_fpbg_trans (G) (L) (T):
      ∀G1,L1,T1. ❪G1,L1,T1❫ ⬂+ ❪G,L,T❫ →
      ∀G2,L2,T2. ❪G,L,T❫ > ❪G2,L2,T2❫ → ❪G1,L1,T1❫ > ❪G2,L2,T2❫.
/3 width=5 by fpbs_fpbg_trans, fqup_fpbs/ qed-.
