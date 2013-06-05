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

include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

include "basic_2/substitution/lpss_ldrop.ma".
include "basic_2/substitution/fsups.ma".

lemma fsup_cpss_trans: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ∀U2. L2 ⊢ T2 ▶* U2 →
                       ∃∃U1. L1 ⊢ T1 ▶* U1 & ⦃L1, U1⦄ ⊃ ⦃L2, U2⦄.
#L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2 [2: * ] [1,2,3,4,5: /3 width=5/ ]
[ * #L1
  [ #V2 #U2 #HVU2
    elim (lift_total U2 0 1) #W2 #HUW2
    @(ex2_intro … W2) /2 width=7/
    @(fsup_ldrop … L1 … HUW2) /2 width=1/
  | #W #U2 #H  
    @(ex2_intro … (#0)) /2 width=7/
  
| #L1 #K1 #K2 #T1 #T2 #U1 #d #e #HLK1 #HTU1 #_ #IHT12 #U2 #HTU2
  elim (IHT12 … HTU2) -IHT12 -HTU2 #T #HT1 #HT2
  elim (lift_total T d e) #U #HTU
  lapply (cpss_lift … HT1 … HLK1 … HTU1 … HTU) -HT1 -HTU1 /3 width=11/
]
qed-.



(*
include "basic_2/relocation/lift_lift.ma".
include "basic_2/substitution/fsups.ma".
*)
(*
lemma fsup_ssta_trans: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ →
                       ∀U2,l. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l+1, U2⦄ →
                       ∃∃L,U1. ⦃h, L1⦄ ⊢ T1 ➡[g] U1 & ⦃L1, U1⦄ ⊃* ⦃L2, U2⦄.

*)
lemma fsup_ssta_trans: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ →
                       ∀U2,l. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l+1, U2⦄ →
                       ∃∃U1. ⦃h, L1⦄ ⊢ T1 ➡[g] U1 & ⦃L1, U1⦄ ⊃ ⦃L2, U2⦄.
#h #g #L1 #L2 #T1 #T2 #H elim H -L1 -L2 -T1 -T2
[ * #L1 #V1 #U2 #l #H
  elim (lift_total U2 0 1) #W2 #HUW2
(*
  [ @(ex2_intro … W2) [ @(cpx_ssta … l) @(ssta_ldef … H) //
                      | @(fsups_ldrop … L1 … HUW2) /2 width=1/ 
*)
|
| #a #I #L1 #V1 #T1 #U2 #l #HT1
  @(ex2_intro … (ⓑ{a,I}V1.U2)) /2 width=1/  
