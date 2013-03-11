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

include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/lsubsv_ldrop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties on stratified native type assignment **************************)

lemma lsubsv_ssta_trans: ∀h,g,L2,T,U2,l. ⦃h, L2⦄ ⊢ T •[g,l] U2 →
                         ∀L1. h ⊢ L1 ⊩:⊑[g] L2 →
                         ∃∃U1. L1 ⊢ U2 ⬌* U1 & ⦃h, L1⦄ ⊢ T •[g,l] U1.
#h #g #L2 #T #U2 #l #H elim H -L2 -T -U2 -l
[ #L2 #k #l #Hkl #L1 #_ /3 width=3/
| #L2 #K2 #V2 #W2 #U2 #i #l #HLK2 #_ #HWU2 #IHVW2 #L1 #HL12
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H *
  [ #K1 #HK12 #H destruct
    elim (IHVW2 … HK12) -K2 #W1 #HW21 #H
    elim (lift_total W1 0 (i+1)) #U1 #HWU1
    lapply (ldrop_fwd_ldrop2 … HLK1) /3 width=9/
  | #K1 #V1 #W1 #l0 #_ #_ #_ #_ #_ #_ #H destruct
  ]
| #L2 #K2 #W2 #V2 #U2 #i #l #HLK2 #_ #HWU2 #IHWV2 #L1 #HL12
  elim (lsubsv_ldrop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H *
  [ #K1 #HK12 #H destruct
    elim (IHWV2 … HK12) -K2 #V1 #_ #H -V2 /3 width=6/
  | #K1 #W1 #V1 #l0 #HV1 #HVW1 #HW21 #HW2 #HK12 #H #_ destruct
    elim (IHWV2 … HK12) -K2 #V #_ #H
    elim (lift_total W1 0 (i+1)) #U1 #HWU1
    lapply (ldrop_fwd_ldrop2 … HLK1) #HLK
    @(ex2_intro … U1)
    [ @(cpcs_lift … HLK … HWU2 … HWU1 HW21)
    | @(ssta_ldef … HLK1 … HWU1) 
  (*  
    /3 width=9/
  *)