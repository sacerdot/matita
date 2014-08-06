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

include "basic_2/equivalence/scpes_aaa.ma".
include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Forward lemmas on lenv refinement for atomic arity assignment ************)

lemma lsubsv_fwd_lsuba: ∀h,g,G,L1,L2. G ⊢ L1 ⫃¡[h, g] L2 → G ⊢ L1 ⫃⁝ L2.
#h #g #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsuba_pair/
#L1 #L2 #W #V #l1 #H #_ #_ #_ #_ #IHL12
elim (shnv_inv_cast … H) -H #HW #HV #H
lapply (H 0 ?) // -l1 #HWV
elim (snv_fwd_aaa … HW) -HW #B #HW
elim (snv_fwd_aaa … HV) -HV #A #HV
lapply (scpes_aaa_mono … HWV … HW … HV) #H destruct
/4 width=5 by lsuba_aaa_conf, lsuba_beta, aaa_cast/
qed-.
