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

include "Basic_2/grammar/aarity.ma".
include "Basic_2/unfold/lifts_vector.ma".
include "Basic_2/computation/acp.ma".

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

(* Note: this is Girard's CR1 *)
definition S1 ≝ λRP,C:lenv→predicate term.
                ∀L,T. C L T → RP L T.

(* Note: this is Tait's iii, or Girard's CR4 *)
definition S2 ≝ λRR:lenv→relation term. λRS:relation term. λRP,C:lenv→predicate term.
                ∀L,Vs. all … (RP L) Vs →
                ∀T. 𝕊[T] → NF … (RR L) RS T → C L (ⒶVs.T).

(* Note: this is Tait's ii *)
definition S3 ≝ λRP,C:lenv→predicate term.
                ∀L,Vs,V,T,W. C L (ⒶVs. 𝕔{Abbr}V. T) → RP L W → C L (ⒶVs. 𝕔{Appl}V. 𝕔{Abst}W. T).

definition S5 ≝ λRP,C:lenv→predicate term.
                ∀L,V1s,V2s. ⇑[0, 1] V1s ≡ V2s →
                ∀V,T. C (L. 𝕓{Abbr}V) (ⒶV2s. T) → RP L V → C L (ⒶV1s. 𝕔{Abbr}V. T).

definition S6 ≝ λRP,C:lenv→predicate term.
                ∀L,Vs,T,W. C L (ⒶVs. T) → RP L W → C L (ⒶVs. 𝕔{Cast}W. T).

definition S7 ≝ λC:lenv→predicate term. ∀L1,L2,T1,T2,d,e.
                C L1 T1 → ⇓[d, e] L2 ≡ L1 → ⇑[d, e] T1 ≡ T2 → C L2 T2.

definition S7s ≝ λC:lenv→predicate term.
                 ∀L1,L2,des. ⇓[des] L2 ≡ L1 →
                 ∀T1,T2. ⇑[des] T1 ≡ T2 → C L1 T1 → C L2 T2.

(* properties of the abstract candidate of reducibility *)
record acr (RR:lenv->relation term) (RS:relation term) (RP,C:lenv→predicate term) : Prop ≝
{ s1: S1 RP C;
  s2: S2 RR RS RP C;
  s3: S3 RP C;
  s5: S5 RP C;
  s6: S6 RP C;
  s7: S7 C
}.

(* the abstract candidate of reducibility associated to an atomic arity *)
let rec aacr (RP:lenv→predicate term) (A:aarity) (L:lenv) on A: predicate term ≝
λT. match A with
[ AAtom     ⇒ RP L T
| APair B A ⇒ ∀L0,V0,T0,des. aacr RP B L0 V0 → ⇓[des] L0 ≡ L → ⇑[des] T ≡ T0 →
              aacr RP A L0 (𝕔{Appl} V0. T0)
].

interpretation
   "candidate of reducibility of an atomic arity (abstract)"
   'InEInt RP L T A = (aacr RP A L T).

(* Basic properties *********************************************************)

lemma acr_lifts: ∀C. S7 C → S7s C.
#C #HC #L1 #L2 #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=9/
]
qed.

lemma rp_lifts: ∀RR,RS,RP. acr RR RS RP (λL,T. RP L T) →
                ∀des,L0,L,V,V0. ⇓[des] L0 ≡ L → ⇑[des] V ≡ V0 →
                RP L V → RP L0 V0.
#RR #RS #RP #HRP #des #L0 #L #V #V0 #HL0 #HV0 #HV 
@acr_lifts /width=6/
@(s7 … HRP)
qed.

lemma rp_liftsv_all: ∀RR,RS,RP. acr RR RS RP (λL,T. RP L T) →
                     ∀des,L0,L,Vs,V0s. ⇑[des] Vs ≡ V0s →  ⇓[des] L0 ≡ L →
                     all … (RP L) Vs → all … (RP L0) V0s.
#RR #RS #RP #HRP #des #L0 #L #Vs #V0s #H elim H -Vs -V0s normalize //
#T1s #T2s #T1 #T2 #HT12 #_ #IHT2s #HL0 * #HT1 #HT1s
@conj /2 width=1/ /2 width=6 by rp_lifts/
qed.

axiom aacr_acr: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                ∀A. acr RR RS RP (aacr RP A).
(*
#RR #RS #RP #H1RP #H2RP #A elim A -A normalize //
#B #A #IHB #IHA @mk_acr normalize
[ #L #T #H
  lapply (H ? (⋆0) ? ⟠ ? ? ?) -H 
  [1,3: // |2,4: skip
  | @(s2 … IHB … ◊) // /2 width=2/
  | #H @(cp3 … H1RP … 0) @(s1 … IHA) //
  ]
| #L #Vs #HVs #T #H1T #H2T #L0 #V0 #X #des #HB #HL0 #H
  elim (lifts_inv_applv1 … H) -H #V0s #T0 #HV0s #HT0 #H destruct
  lapply (s1 … IHB … HB) #HV0
  @(s2 … IHA … (V0 :: V0s)) /2 width=4 by lifts_simple_dx/ /3 width=6/
| #L #Vs #U #T #W #HA #HW #L0 #V0 #X #des #HB #HL0 #H
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #U0 #X #HU0 #HX #H destruct
  elim (lifts_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT0 #H destruct
  @(s3 … IHA … (V0 :: V0s)) /2 width=6 by rp_lifts/ /4 width=5/
| #L #V1s #V2s #HV12s #V #T #HA #HV #L0 #V10 #X #des #HB #HL0 #H
  elim (lifts_inv_applv1 … H) -H #V10s #Y #HV10s #HY #H destruct
  elim (lifts_inv_bind1 … HY) -HY #V0 #T0 #HV0 #HT0 #H destruct
  elim (lift_total V10 0 1) #V20 #HV120
  elim (liftv_total 0 1 V10s) #V20s #HV120s
  @(s5 … IHA … (V10 :: V10s) (V20 :: V20s)) /2 width=1/ /2 width=6 by rp_lifts/
  @(HA … (ss des)) /2 width=1/
  [ @(s7 … IHB … HB … HV120) /2 width=1/
  | @liftsv_applv //
  ]
| #L #Vs #T #W #HA #HW #L0 #V0 #X #des #HB #HL0 #H
  elim (lifts_inv_applv1 … H) -H #V0s #Y #HV0s #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #W0 #T0 #HW0 #HT0 #H destruct
  @(s6 … IHA … (V0 :: V0s)) /2 width=6 by rp_lifts/ /3 width=4/ 
| /3 width=7/
]
qed.
*)
lemma aacr_abst: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                 ∀L,W,T,A,B. RP L W → (
                    ∀L0,V0,T0,des. ⇓[des] L0 ≡ L → ⇑[ss des] T ≡ T0 →
                                   ⦃L0, V0⦄ [RP] ϵ 〚B〛→ ⦃L0. 𝕓{Abbr} V0, T0⦄ [RP] ϵ 〚A〛
                 ) →
                 ⦃L, 𝕓{Abst} W. T⦄ [RP] ϵ 〚𝕔 B. A〛.
#RR #RS #RP #H1RP #H2RP #L #W #T #A #B #HW #HA #L0 #V0 #X #des #HB #HL0 #H
lapply (aacr_acr … H1RP H2RP A) #HCA
lapply (aacr_acr … H1RP H2RP B) #HCB
elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
lapply (s1 … HCB) -HCB #HCB 
@(s3 … HCA … ◊) /2 width=6 by rp_lifts/
@(s5 … HCA … ◊ ◊) // /2 width=1/ /2 width=3/
qed.
