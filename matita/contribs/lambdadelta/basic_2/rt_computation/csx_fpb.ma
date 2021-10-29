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

include "basic_2/rt_transition/fpb_lpx.ma".
include "basic_2/rt_computation/csx_fqus.ma".
include "basic_2/rt_computation/csx_reqg.ma".
include "basic_2/rt_computation/csx_lpx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with parallel rst-transition for closures *********************)

(* Basic_2A1: was: csx_fpb_conf *)
lemma csx_fpb_conf:
      ∀G1,L1,T1. ❨G1,L1❩ ⊢ ⬈*𝐒 T1 →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩ → ❨G2,L2❩ ⊢ ⬈*𝐒 T2.
#G1 #L1 #T1 #HT1 #G2 #L2 #T2 #H
elim (fpb_inv_req … H) -H #L0 #L #T #H1 #HT2 #HL0 #HL02
lapply (cpx_reqg_conf … HL0 … HT2) -HT2 // #HT2
/5 width=8 by csx_fquq_conf, csx_cpx_trans, csx_lpx_conf, csx_reqg_conf/
qed-.
