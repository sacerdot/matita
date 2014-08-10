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

include "basic_2/notation/relations/ineint_5.ma".
include "basic_2/grammar/aarity.ma".
include "basic_2/multiple/mr2_mr2.ma".
include "basic_2/multiple/lifts_lift_vector.ma".
include "basic_2/multiple/drops_drop.ma".
include "basic_2/computation/gcp.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

definition S0 ≝ λC:candidate. ∀G,L2,L1,T1,d,e.
                C G L1 T1 → ∀T2. ⇩[Ⓕ, d, e] L2 ≡ L1 → ⇧[d, e] T1 ≡ T2 → C G L2 T2.

definition S0s ≝ λC:candidate.
                 ∀G,L1,L2,des. ⇩*[Ⓕ, des] L2 ≡ L1 →
                 ∀T1,T2. ⇧*[des] T1 ≡ T2 → C G L1 T1 → C G L2 T2.

(* Note: this is Girard's CR1 *)
definition S1 ≝ λRP,C:candidate.
                ∀G,L,T. C G L T → RP G L T.

(* Note: this is Tait's iii, or Girard's CR4 *)
definition S2 ≝ λRR:relation4 genv lenv term term. λRS:relation term. λRP,C:candidate.
                ∀G,L,Vs. all … (RP G L) Vs →
                ∀T. 𝐒⦃T⦄ → NF … (RR G L) RS T → C G L (ⒶVs.T).

(* Note: this generalizes Tait's ii *)
definition S3 ≝ λC:candidate.
                ∀a,G,L,Vs,V,T,W.
                C G L (ⒶVs.ⓓ{a}ⓝW.V.T) → C G L (ⒶVs.ⓐV.ⓛ{a}W.T).

definition S4 ≝ λRP,C:candidate.
                ∀G,L,Vs. all … (RP G L) Vs → ∀k. C G L (ⒶVs.⋆k).

definition S5 ≝ λC:candidate. ∀I,G,L,K,Vs,V1,V2,i.
                C G L (ⒶVs.V2) → ⇧[0, i+1] V1 ≡ V2 →
                ⇩[i] L ≡ K.ⓑ{I}V1 → C G L (ⒶVs.#i).

definition S6 ≝ λRP,C:candidate.
                ∀G,L,V1s,V2s. ⇧[0, 1] V1s ≡ V2s →
                ∀a,V,T. C G (L.ⓓV) (ⒶV2s.T) → RP G L V → C G L (ⒶV1s.ⓓ{a}V.T).

definition S7 ≝ λC:candidate.
                ∀G,L,Vs,T,W. C G L (ⒶVs.T) → C G L (ⒶVs.W) → C G L (ⒶVs.ⓝW.T).

(* requirements for the generic reducibility candidate *)
record gcr (RR:relation4 genv lenv term term) (RS:relation term) (RP,C:candidate) : Prop ≝
{ s0: S0 C;
  s1: S1 RP C;
  s2: S2 RR RS RP C;
  s3: S3 C;
  s4: S4 RP C;
  s5: S5 C;
  s6: S6 RP C;
  s7: S7 C
}.

(* the functional construction for candidates *)
definition cfun: candidate → candidate → candidate ≝
                 λC1,C2,G,K,T. ∀L,V,U,des.
                 ⇩*[Ⓕ, des] L ≡ K → ⇧*[des] T ≡ U → C1 G L V → C2 G L (ⓐV.U).

(* the reducibility candidate associated to an atomic arity *)
let rec acr (RP:candidate) (A:aarity) on A: candidate ≝
match A with
[ AAtom     ⇒ RP
| APair B A ⇒ cfun (acr RP B) (acr RP A)
].

interpretation
   "candidate of reducibility of an atomic arity (abstract)"
   'InEInt RP G L T A = (acr RP A G L T).

(* Basic properties *********************************************************)

(* Basic_1: was: sc3_lift1 *)
lemma gcr_lifts: ∀C. S0 C → S0s C.
#C #HC #G #L1 #L2 #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1 <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=10 by/
]
qed.

lemma rp_lifts: ∀RR,RS,RP. gcr RR RS RP RP →
                ∀des,G,L0,L,V,V0. ⇩*[Ⓕ, des] L0 ≡ L → ⇧*[des] V ≡ V0 →
                RP G L V → RP G L0 V0.
#RR #RS #RP #HRP #des #G #L0 #L #V #V0 #HL0 #HV0 #HV
@gcr_lifts /width=7 by/
@(s0 … HRP)
qed.

(* Basic_1: was only: sns3_lifts1 *)
lemma rp_liftsv_all: ∀RR,RS,RP. gcr RR RS RP RP →
                     ∀des,G,L0,L,Vs,V0s. ⇩*[Ⓕ, des] L0 ≡ L → ⇧*[des] Vs ≡ V0s →
                     all … (RP G L) Vs → all … (RP G L0) V0s.
#RR #RS #RP #HRP #des #G #L0 #L #Vs #V0s #HL0 #H elim H -Vs -V0s normalize //
#T1s #T2s #T1 #T2 #HT12 #_ #IHT2s * /3 width=7 by rp_lifts, conj/
qed.

(* Basic_1: was:
   sc3_sn3 sc3_abst sc3_appl sc3_abbr sc3_bind sc3_cast sc3_lift
*)
lemma acr_gcr: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
               ∀A. gcr RR RS RP (acr RP A).
#RR #RS #RP #H1RP #H2RP #A elim A -A normalize //
#B #A #IHB #IHA @mk_gcr normalize
[ /3 width=7 by drops_cons, lifts_cons/
| #G #L #T #H
  elim (cp1 … H1RP G L) #k #HK
  lapply (H ? (⋆k) ? (⟠) ? ? ?) -H
  [3,5: // |2,4: skip
  | @(s2 … IHB … (◊)) //
  | #H @(cp2 … H1RP … k) @(s1 … IHA) //
  ]
| #G #L #Vs #HVs #T #H1T #H2T #L0 #V0 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #T0 #HV0s #HT0 #H destruct
  lapply (s1 … IHB … HB) #HV0
  @(s2 … IHA … (V0 @ V0s))
  /3 width=14 by rp_liftsv_all, gcp_lifts, cp0, lifts_simple_dx, conj/
| #a #G #L #Vs #U #T #W #HA #L0 #V0 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #U0 #X #HU0 #HX #H destruct
  elim (lifts_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT0 #H destruct
  @(s3 … IHA … (V0 @ V0s)) /5 width=6 by lifts_applv, lifts_flat, lifts_bind/
| #G #L #Vs #HVs #k #L0 #V0 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  >(lifts_inv_sort1 … HY) -Y
  lapply (s1 … IHB … HB) #HV0
  @(s4 … IHA … (V0 @ V0s)) /3 width=7 by rp_liftsv_all, conj/
| #I #G #L #K #Vs #V1 #V2 #i #HA #HV12 #HLK #L0 #V0 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  elim (lifts_inv_lref1 … HY) -HY #i0 #Hi0 #H destruct
  elim (drops_drop_trans … HL0 … HLK) #X #des0 #i1 #HL02 #H #Hi1 #Hdes0
  >(at_mono … Hi1 … Hi0) in HL02; -i1 #HL02
  elim (drops_inv_skip2 … Hdes0 … H) -H -des0 #L2 #W1 #des0 #Hdes0 #HLK #HVW1 #H destruct
  elim (lift_total W1 0 (i0 + 1)) #W2 #HW12
  elim (lifts_lift_trans  … Hdes0 … HVW1 … HW12) // -Hdes0 -Hi0 #V3 #HV13 #HVW2
  >(lift_mono … HV13 … HV12) in HVW2; -V3 #HVW2
  @(s5 … IHA … (V0 @ V0s) … HW12 HL02) /3 width=5 by lifts_applv/
| #G #L #V1s #V2s #HV12s #a #V #T #HA #HV #L0 #V10 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V10s #Y #HV10s #HY #H destruct
  elim (lifts_inv_bind1 … HY) -HY #V0 #T0 #HV0 #HT0 #H destruct
  elim (lift_total V10 0 1) #V20 #HV120
  elim (liftv_total 0 1 V10s) #V20s #HV120s
  @(s6 … IHA … (V10 @ V10s) (V20 @ V20s)) /3 width=7 by rp_lifts, liftv_cons/
  @(HA … (des + 1)) /2 width=2 by drops_skip/
  [ @lifts_applv //
    elim (liftsv_liftv_trans_le … HV10s … HV120s) -V10s #V10s #HV10s #HV120s
    >(liftv_mono … HV12s … HV10s) -V1s //
  | @(s0 … IHB … HB … HV120) /2 width=2 by drop_drop/
  ]
| #G #L #Vs #T #W #HA #HW #L0 #V0 #X #des #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #W0 #T0 #HW0 #HT0 #H destruct
  @(s7 … IHA … (V0 @ V0s)) /3 width=5 by lifts_applv/
]
qed.

lemma acr_abst: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
                ∀a,G,L,W,T,A,B. ⦃G, L, W⦄ ϵ[RP] 〚B〛 → (
                   ∀L0,V0,W0,T0,des. ⇩*[Ⓕ, des] L0 ≡ L → ⇧*[des] W ≡ W0 → ⇧*[des + 1] T ≡ T0 →
                                   ⦃G, L0, V0⦄ ϵ[RP] 〚B〛 → ⦃G, L0, W0⦄ ϵ[RP] 〚B〛 → ⦃G, L0.ⓓⓝW0.V0, T0⦄ ϵ[RP] 〚A〛
                ) →
                ⦃G, L, ⓛ{a}W.T⦄ ϵ[RP] 〚②B.A〛.
#RR #RS #RP #H1RP #H2RP #a #G #L #W #T #A #B #HW #HA #L0 #V0 #X #des #HL0 #H #HB
lapply (acr_gcr … H1RP H2RP A) #HCA
lapply (acr_gcr … H1RP H2RP B) #HCB
elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
lapply (gcr_lifts … HL0 … HW0 HW) -HW [ @(s0 … HCB) ] #HW0
@(s3 … HCA … (◊))
@(s6 … HCA … (◊) (◊)) //
[ @(HA … HL0) //
| lapply (s1 … HCB) -HCB #HCB
  @(s7 … H2RP … (◊)) /2 width=1 by/
]
qed.

(* Basic_1: removed theorems 2: sc3_arity_gen sc3_repl *)
(* Basic_1: removed local theorems 1: sc3_sn3_abst *)
