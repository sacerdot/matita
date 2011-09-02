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

include "Basic-2/substitution/tps_tps.ma".
include "Basic-2/reduction/ltpr_drop.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

axiom tpr_tps_ltpr: ∀T1,T2. T1 ⇒ T2 →
                    ∀L1,d,e,U1. L1 ⊢ T1 [d, e] ≫ U1 →
                    ∀L2. L1 ⇒ L2 →
                    ∃∃U2. U1 ⇒ U2 & L2 ⊢ T2 [d, e] ≫ U2.
(*
#T1 #T2 #H elim H -H T1 T2
[ #I #L1 #d #e #X #H
  elim (tps_inv_atom1 … H) -H
  [ #H destruct -X /2/
  | * #K1 #V1 #i #Hdi #Hide #HLK1 #HVU1 #H #L2 #HL12 destruct -I;
    elim (ltpr_drop_conf … HLK1 … HL12) -HLK1 HL12 #X #HLK2 #H
    elim (ltpr_inv_pair1 … H) -H #K2 #V2 #_ #HV12 #H destruct -X;
    elim (lift_total V2 0 (i+1)) #U2 #HVU2
    lapply (tpr_lift … HV12 … HVU1 … HVU2) -HV12 HVU1 #HU12
    @ex2_1_intro [2: @HU12 | skip | /2/ ] (**) (* /3 width=6/ is too slow *)
  ]
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct -X;
  elim (IHV12 … HVW1 … HL12) -IHV12 HVW1;
  elim (IHT12 … HTU1 … HL12) -IHT12 HTU1 HL12 /3 width=5/
| #V1 #V2 #W #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_flat1 … H) -H #VV1 #Y #HVV1 #HY #HX destruct -X;
  elim (tps_inv_bind1 … HY) -HY #WW #TT1 #_ #HTT1 #H destruct -Y;
  elim (IHV12 … HVV1 … HL12) -IHV12 HVV1 #VV2 #HVV12 #HVV2
  elim (IHT12 … HTT1 (L2. 𝕓{Abst} W) ?) -IHT12 HTT1 /2/ -HL12 #TT2 #HTT12 #HTT2
  lapply (tps_leq_repl … HTT2 (L2. 𝕓{Abbr} V2) ?) -HTT2 /3 width=5/
| #I #V1 #V2 #T1 #T2 #U2 #HV12 #_ #HTU2 #IHV12 #IHT12 #L1 #d #e #X #H #L2 #HL12
  elim (tps_inv_bind1 … H) -H #VV1 #TT1 #HVV1 #HTT1 #H destruct -X;
  elim (IHV12 … HVV1 … HL12) -IHV12 HVV1 #VV2 #HVV12 #HVV2
  elim (IHT12 … HTT1 (L2. 𝕓{I} V2) ?) -IHT12 HTT1 /2/ -HL12 #TT2 #HTT12 #HTT2
(*lapply (tps_leq_repl … HTT2 (L2. 𝕓{I} VV2) ?) -HTT2 /2/ #HTT2 *)
  elim (tps_conf_neq … HTU2 … HTT2 ?) -HTU2 HTT2 T2 /2/ #T2 #HUT2 #HTT2
  @ex2_1_intro
  [2: @tpr_delta [4: @HVV12 |5: @HTT12 |1,2: skip |6: ] (*|6: ]1,2: skip ]*)
  |1: skip
  |3: @tps_bind [@HVV2 | @HUT2 ]
  ]
*)

lemma tpr_tps_bind: ∀I,V1,V2,T1,T2,U1. V1 ⇒ V2 → T1 ⇒ T2 →
                    ⋆. 𝕓{I} V1 ⊢ T1 [0, 1] ≫ U1 →
                    ∃∃U2. U1 ⇒ U2 & ⋆. 𝕓{I} V2 ⊢ T2 [0, 1] ≫ U2.
/3 width=7/ qed.
