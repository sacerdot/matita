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

include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/lsubsv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Forward lemmas on lenv refinement for atomic arity assignment ************)

lemma lsubsv_fwd_lsuba: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 → G ⊢ L1 ⁝⊑ L2.
#h #g #G #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
#L1 #L2 #W #V #l #H1W #HV #HVW #H2W #H1l #_ #_ #IHL12
lapply (snv_scast … HV H1W HVW H1l) -HV -H1W -HVW -H1l #HV
elim (snv_fwd_aaa … HV) -HV #A #HV
elim (snv_fwd_aaa … H2W) -H2W #B #HW
elim (aaa_inv_cast … HV) #HWA #_
lapply (lsuba_aaa_trans … HW … IHL12) #HWB
lapply (aaa_mono … HWB … HWA) -HWB -HWA #H destruct /2 width=3/
qed-.
