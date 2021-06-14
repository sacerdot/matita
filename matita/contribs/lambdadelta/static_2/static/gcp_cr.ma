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

include "static_2/notation/relations/inwbrackets_5.ma".
include "static_2/syntax/aarity.ma".
include "static_2/relocation/lifts_simple.ma".
include "static_2/relocation/lifts_lifts_vector.ma".
include "static_2/relocation/drops_drops.ma".
include "static_2/static/gcp.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

(* Note: this is Girard's CR1 *)
definition S1 ≝ λRP,C:candidate.
                ∀G,L,T. C G L T → RP G L T.

(* Note: this is Tait's iii, or Girard's CR4 *)
definition S2 ≝ λRR:relation4 genv lenv term term. λRS:relation term. λRP,C:candidate.
                ∀G,L,Vs. all … (RP G L) Vs →
                ∀T. 𝐒❪T❫ → nf RR RS G L T → C G L (ⒶVs.T).

(* Note: this generalizes Tait's ii, or Girard's CR3 *)
definition S3 ≝ λC:candidate.
                ∀a,G,L,Vs,V,T,W.
                C G L (ⒶVs.ⓓ[a]ⓝW.V.T) → C G L (ⒶVs.ⓐV.ⓛ[a]W.T).

definition S5 ≝ λC:candidate. ∀I,G,L,K,Vs,V1,V2,i.
                C G L (ⒶVs.V2) → ⇧[↑i] V1 ≘ V2 →
                ⇩[i] L ≘ K.ⓑ[I]V1 → C G L (ⒶVs.#i).

definition S6 ≝ λRP,C:candidate.
                ∀G,L,V1b,V2b. ⇧[1] V1b ≘ V2b →
                ∀a,V,T. C G (L.ⓓV) (ⒶV2b.T) → RP G L V → C G L (ⒶV1b.ⓓ[a]V.T).

definition S7 ≝ λC:candidate.
                ∀G,L,Vs,T,W. C G L (ⒶVs.T) → C G L (ⒶVs.W) → C G L (ⒶVs.ⓝW.T).

(* requirements for the generic reducibility candidate *)
record gcr (RR:relation4 genv lenv term term) (RS:relation term) (RP,C:candidate) : Prop ≝
{ s1: S1 RP C;
  s2: S2 RR RS RP C;
  s3: S3 C;
  s5: S5 C;
  s6: S6 RP C;
  s7: S7 C
}.

(* the functional construction for candidates *)
definition cfun: candidate → candidate → candidate ≝
                 λC1,C2,G,K,T. ∀f,L,W,U.
                 ⇩*[Ⓕ,f] L ≘ K → ⇧*[f] T ≘ U → C1 G L W → C2 G L (ⓐW.U).

(* the reducibility candidate associated to an atomic arity *)
rec definition acr (RP:candidate) (A:aarity) on A: candidate ≝
match A with
[ AAtom     ⇒ RP
| APair B A ⇒ cfun (acr RP B) (acr RP A)
].

interpretation
   "reducibility candidate of an atomic arity (abstract)"
   'InWBrackets RP G L T A = (acr RP A G L T).

(* Basic properties *********************************************************)

(* Note: this requires Ⓕ-slicing in cfun since b is unknown in d_liftable_1 *)
(* Note: this requires multiple relocation *)
(* Basic 1: includes: sc3_lift *)
(* Basic 2A1: includes: gcr_lift *)
(* Basic 2A1: note: gcr_lift should be acr_lift *)
(* Basic_1: was: sc3_lift1 *)
(* Basic 2A1: was: gcr_lifts *)
(* Basic 2A1: note: gcr_lifts should be acr_lifts *)
lemma acr_lifts: ∀RR,RS,RP. gcp RR RS RP → ∀A,G. d_liftable1 (acr RP A G).
#RR #RS #RP #H #A #G elim A -A
[ /2 width=7 by cp2/
| #B #A #HB #HA #K #T #HKT #b #f #L #HLK #U #HTU #f0 #L0 #W #U0 #HL0 #HU0 #HW
  lapply (drops_trans … HL0 … HLK ??) [3:|*: // ] -L #HL0K
  lapply (lifts_trans … HTU … HU0 ??) [3:|*: // ] -U #HTU0
  /2 width=3 by/ (**) (* full auto fails *)
]
qed-.

(* Basic_1: was:
   sc3_sn3 sc3_abst sc3_appl sc3_abbr sc3_bind sc3_cast
*)
(* Note: one sort must exist *)
lemma acr_gcr: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
               ∀A. gcr RR RS RP (acr RP A).
#RR #RS #RP #H1RP #H2RP #A elim A -A //
#B #A #IHB #IHA @mk_gcr
[ #G #L #T #H
  letin s ≝ 0 (* one sort must exist *)
  lapply (cp1 … H1RP G L s) #HK
  lapply (s2 … IHB G L (Ⓔ) … HK) // #HB
  lapply (H (𝐢) L (⋆s) T ? ? ?) -H
  /3 width=6 by s1, cp3, drops_refl, lifts_refl/
| #G #L #Vs #HVs #T #H1T #H2T #f #L0 #V0 #X #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #T0 #HV0s #HT0 #H destruct
  lapply (s1 … IHB … HB) #HV0
  @(s2 … IHA  … (V0⨮V0s)) /3 width=13 by cp0, gcp2_all, lifts_simple_dx, conj/
| #p #G #L #Vs #U #T #W #HA #f #L0 #V0 #X #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #X0 #HV0s #H0 #H destruct
  elim (lifts_inv_flat1 … H0) -H0 #U0 #X #HU0 #HX #H destruct
  elim (lifts_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT0 #H destruct
  @(s3 … IHA … (V0⨮V0s)) /5 width=6 by lifts_applv, lifts_flat, lifts_bind/
| #I #G #L #K #Vs #V1 #V2 #i #HA #HV12 #HLK #f #L0 #V0 #X #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #X0 #HV0s #H0 #H destruct
  elim (lifts_inv_lref1 … H0) -H0 #j #Hf #H destruct
  lapply (drops_trans … HL0 … HLK ??) [3: |*: // ] -HLK #H
  elim (drops_split_trans … H) -H [ |*: /2 width=6 by after_uni_dx/ ] #Y #HLK0 #HY
  lapply (drops_tls_at … Hf … HY) -HY #HY
  elim (drops_inv_skip2 … HY) -HY #Z #K0 #HK0 #HZ #H destruct
  elim (liftsb_inv_pair_sn … HZ) -HZ #W1 #HVW1 #H destruct
  elim (lifts_total W1 (𝐔❨↑j❩)) #W2 #HW12
  lapply (lifts_trans … HVW1 … HW12 ??) -HVW1 [3: |*: // ] #H
  lapply (lifts_conf … HV12 … H f ?) -V1 [ /2 width=3 by after_uni_succ_sn/ ] #HVW2
  @(s5 … IHA … (V0⨮V0s) … HW12) /3 width=4 by drops_inv_gen, lifts_applv/
| #G #L #V1s #V2s #HV12s #p #V #T #HA #HV #f #L0 #V10 #X #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V10s #X0 #HV10s #H0 #H destruct
  elim (lifts_inv_bind1 … H0) -H0 #V0 #T0 #HV0 #HT0 #H destruct
  elim (lifts_total V10 (𝐔❨1❩)) #V20 #HV120
  elim (liftsv_total (𝐔❨1❩) V10s) #V20s #HV120s
  @(s6 … IHA … (V10⨮V10s) (V20⨮V20s)) /3 width=7 by cp2, liftsv_cons/
  @(HA … (⫯f)) /3 width=2 by drops_skip, ext2_pair/
  [ @lifts_applv //
    lapply (liftsv_trans … HV10s … HV120s ??) -V10s [3: |*: // ] #H
    elim (liftsv_split_trans … H (𝐔❨1❩) (⫯f)) /2 width=1 by after_uni_one_sn/ #V10s #HV10s #HV120s
    >(liftsv_mono … HV12s … HV10s) -V1s //
  | @(acr_lifts … H1RP … HB … HV120) /3 width=2 by drops_refl, drops_drop/
  ]
| #G #L #Vs #T #W #HA #HW #f #L0 #V0 #X #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0s #X0 #HV0s #H0 #H destruct
  elim (lifts_inv_flat1 … H0) -H0 #W0 #T0 #HW0 #HT0 #H destruct
  @(s7 … IHA … (V0⨮V0s)) /3 width=5 by lifts_applv/
]
qed.

lemma acr_abst: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
                ∀p,G,L,W,T,A,B. ❪G,L,W❫ ϵ ⟦B⟧[RP] → (
                   ∀b,f,L0,V0,W0,T0. ⇩*[b,f] L0 ≘ L → ⇧*[f] W ≘ W0 → ⇧*[⫯f] T ≘ T0 →
                                   ❪G,L0,V0❫ ϵ ⟦B⟧[RP] → ❪G,L0,W0❫ ϵ ⟦B⟧[RP] → ❪G,L0.ⓓⓝW0.V0,T0❫ ϵ ⟦A⟧[RP]
                ) →
                ❪G,L,ⓛ[p]W.T❫ ϵ ⟦②B.A⟧[RP].
#RR #RS #RP #H1RP #H2RP #p #G #L #W #T #A #B #HW #HA #f #L0 #V0 #X #HL0 #H #HB
lapply (acr_gcr … H1RP H2RP A) #HCA
lapply (acr_gcr … H1RP H2RP B) #HCB
elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
lapply (acr_lifts … H1RP … HW … HL0 … HW0) -HW #HW0
lapply (s3 … HCA … p G L0 (Ⓔ)) #H @H -H
lapply (s6 … HCA G L0 (Ⓔ) (Ⓔ) ?) // #H @H -H
[ @(HA … HL0) //
| lapply (s1 … HCB) -HCB #HCB
  lapply (s7 … H2RP G L0 (Ⓔ)) /3 width=1 by/
]
qed.

(* Basic_1: removed theorems 2: sc3_arity_gen sc3_repl *)
(* Basic_1: removed local theorems 1: sc3_sn3_abst *)
