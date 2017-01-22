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

include "basic_2/substitution/lpss_ldrop.ma".
include "basic_2/static/ssta_lift.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Properties about sn parallel substitution ********************************)

(* Note: apparently this was missing in basic_1 *)
lemma ssta_cpss_lpss_conf: ∀h,g,L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                           ∀T2. L1 ⊢ T1 ▶* T2 → ∀L2. L1 ⊢ ▶* L2 →
                           ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L1 ⊢ U1 ▶* U2.
#h #g #L1 #T1 #U1 #l #H elim H -L1 -T1 -U1 -l
[ #L1 #k1 #l1 #Hkl1 #X #H
  >(cpss_inv_sort1 … H) -H /3 width=3/
| #L1 #K1 #V1 #W1 #U1 #i #l #HLK1 #_ #HWU1 #IHVW1 #X #H #L2 #HL12
  elim (cpss_inv_lref1 … H) -H
  [ #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK1) -HLK1 #HLK1
    elim (IHVW1 … HV12 … HK12) -IHVW1 -HV12 -HK12 #W2 #HVW2 #HW12
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (cpss_lift … HW12 … HLK1 … HWU1 … HWU2) -HW12 -HLK1 -HWU1 /3 width=6/
  | * #Y #Z #V2 #H #HV12 #HV2
    lapply (ldrop_mono … H … HLK1) -H #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -HL12 #Z #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #V0 #HK12 #_ #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK2) -V0 #HLK2
    lapply (ldrop_fwd_ldrop2 … HLK1) -HLK1 #HLK1
    elim (IHVW1 … HV12 … HK12) -IHVW1 -HK12 -HV12 #W2 #HVW2 #HW12
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (ssta_lift … HVW2 … HLK2 … HV2 … HWU2) -HVW2 -HLK2 -HV2
    lapply (cpss_lift … HW12 … HLK1 … HWU1 … HWU2) -HW12 -HLK1 -HWU1 -HWU2 /3 width=3/
  ]
| #L1 #K1 #W1 #V1 #U1 #i #l #HLK1 #_ #HWU1 #IHWV1 #X #H #L2 #HL12
  elim (cpss_inv_lref1 … H) -H [ | -IHWV1 -HWU1 -HL12 ]
  [ #H destruct
    elim (lpss_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
    elim (lpss_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
    lapply (ldrop_fwd_ldrop2 … HLK1) -HLK1 #HLK1
    elim (IHWV1 … HW12 … HK12) -IHWV1 -HK12 #V2 #HWV2 #_
    elim (lift_total W2 0 (i+1)) #U2 #HWU2
    lapply (cpss_lift … HW12 … HLK1 … HWU1 … HWU2) -HW12 -HLK1 -HWU1 /3 width=6/ 
  | * #K2 #V2 #W2 #HLK2 #_ #_
    lapply (ldrop_mono … HLK2 … HLK1) -HLK1 -HLK2 #H destruct
  ]
| #a #I #L1 #V1 #T1 #U1 #l #_ #IHTU1 #X #H #L2 #HL12
  elim (cpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IHTU1 … HT12 (L2.ⓑ{I}V2)) -IHTU1 -HT12 /2 width=1/ -HL12 /3 width=5/
| #L1 #V1 #T1 #U1 #l #_ #IHTU1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IHTU1 … HT12 … HL12) -IHTU1 -HT12 -HL12 /3 width=5/
| #L1 #W1 #T1 #U1 #l #_ #IHTU1 #X #H #L2 #HL12
  elim (cpss_inv_flat1 … H) -H #W2 #T2 #HW12 #HT12 #H destruct
  elim (IHTU1 … HT12 … HL12) -IHTU1 -HT12 -HL12 /3 width=3/
]
qed-.

lemma ssta_cpss_conf: ∀h,g,L,T1,U1,l. ⦃h, L⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                      ∀T2. L ⊢ T1 ▶* T2 →
                      ∃∃U2. ⦃h, L⦄ ⊢ T2 •[g] ⦃l, U2⦄ & L ⊢ U1 ▶* U2.
/2 width=3 by ssta_cpss_lpss_conf/ qed-.

lemma ssta_lpss_conf: ∀h,g,L1,T,U1,l. ⦃h, L1⦄ ⊢ T •[g] ⦃l, U1⦄ →
                      ∀L2. L1 ⊢ ▶* L2 →
                      ∃∃U2. ⦃h, L2⦄ ⊢ T •[g] ⦃l, U2⦄ & L1 ⊢ U1 ▶* U2.
/2 width=3 by ssta_cpss_lpss_conf/ qed-.
