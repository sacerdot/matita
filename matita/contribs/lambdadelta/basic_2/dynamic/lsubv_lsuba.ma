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

include "basic_2/dynamic/cnv_aaa.ma".
include "basic_2/dynamic/lsubv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Forward lemmas with lenv refinement for atomic arity assignment **********)

(* Basic_2A1: uses: lsubsv_fwd_lsuba *)
lemma lsubsv_fwd_lsuba (h) (a) (G): ∀L1,L2. G ⊢ L1 ⫃![h,a] L2 → G ⊢ L1 ⫃⁝ L2.
#h #a #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsuba_bind/
#L1 #L2 #W #V #H #_ #IH
elim (cnv_inv_cast … H) -H #W0 #HW #HV #HW0 #HVW0
elim (cnv_fwd_aaa … HW) -HW #B #HW
elim (cnv_fwd_aaa … HV) -HV #A #HV
lapply (cpms_aaa_conf … HW … HW0) -HW0 #H
lapply (cpms_aaa_conf … HV … HVW0) -HVW0 #HW0
lapply (aaa_mono … H … HW0) -W0 #H destruct
/4 width=5 by lsuba_aaa_conf, lsuba_beta, aaa_cast/
qed-.
