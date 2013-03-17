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

(* Properties on local environment refinement for atomic arity assignment ***)

lemma lsubsv_fwd_lsuba: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[g] L2 → L1 ⁝⊑ L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
#L1 #L2 #V1 #V2 #W1 #W2 #l #HV1 #HVW1 #HW12 #HW2 #_ #_ #HL12
elim (snv_fwd_aaa … HV1) -HV1 #A #HV1
elim (snv_fwd_aaa … HW2) -HW2 #B #HW2
lapply (ssta_aaa … HV1 … HVW1) -HVW1 #H1
lapply (lsuba_aaa_trans … HW2 … HL12) #H2
lapply (aaa_cpcs_mono … HW12 … H1 … H2) -W1 -H2 #H destruct /2 width=3/
qed-.
