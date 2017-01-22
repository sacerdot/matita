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
include "basic_2/syntax/aarity.ma".
include "basic_2/multiple/mr2_mr2.ma".
include "basic_2/multiple/lifts_lift_vector.ma".
include "basic_2/multiple/drops_drop.ma".
include "basic_2/computation/gcp.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

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
                ∀G,L,Vs. all … (RP G L) Vs → ∀s. C G L (ⒶVs.⋆s).

definition S5 ≝ λC:candidate. ∀I,G,L,K,Vs,V1,V2,i.
                C G L (ⒶVs.V2) → ⬆[0, i+1] V1 ≡ V2 →
                ⬇[i] L ≡ K.ⓑ{I}V1 → C G L (ⒶVs.#i).

definition S6 ≝ λRP,C:candidate.
                ∀G,L,V1b,V2b. ⬆[0, 1] V1b ≡ V2b →
                ∀a,V,T. C G (L.ⓓV) (ⒶV2b.T) → RP G L V → C G L (ⒶV1b.ⓓ{a}V.T).

definition S7 ≝ λC:candidate.
                ∀G,L,Vs,T,W. C G L (ⒶVs.T) → C G L (ⒶVs.W) → C G L (ⒶVs.ⓝW.T).

(* requirements for the generic reducibility candidate *)
record gcr (RR:relation4 genv lenv term term) (RS:relation term) (RP,C:candidate) : Prop ≝
{ b1: S1 RP C;
  b2: S2 RR RS RP C;
  b3: S3 C;
  b4: S4 RP C;
  b5: S5 C;
  b6: S6 RP C;
  b7: S7 C
}.

(* the functional construction for candidates *)
definition cfun: candidate → candidate → candidate ≝
                 λC1,C2,G,K,T. ∀L,W,U,cs.
                 ⬇*[Ⓕ, cs] L ≡ K → ⬆*[cs] T ≡ U → C1 G L W → C2 G L (ⓐW.U).

(* the reducibility candidate associated to an atomic arity *)
rec definition acr (RP:candidate) (A:aarity) on A: candidate ≝
match A with
[ AAtom     ⇒ RP
| APair B A ⇒ cfun (acr RP B) (acr RP A)
].

interpretation
   "candidate of reducibility of an atomic arity (abstract)"
   'InEInt RP G L T A = (acr RP A G L T).

(* Basic properties *********************************************************)

(* Basic 1: was: sc3_lift *)
lemma gcr_lift: ∀RR,RS,RP. gcp RR RS RP → ∀A,G. d_liftable1 (acr RP A G) (Ⓕ).
#RR #RS #RP #H #A elim A -A
/3 width=8 by cp2, drops_cons, lifts_cons/
qed.

(* Basic_1: was: sc3_lift1 *)
lemma gcr_lifts: ∀RR,RS,RP. gcp RR RS RP → ∀A,G. d_liftables1 (acr RP A G) (Ⓕ).
#RR #RS #RP #H #A #G @d1_liftable_liftables /2 width=7 by gcr_lift/
qed.

(* Basic_1: was:
   sc3_sn3 sc3_abst sc3_appl sc3_abbr sc3_bind sc3_cast
*)
lemma acr_gcr: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
               ∀A. gcr RR RS RP (acr RP A).
#RR #RS #RP #H1RP #H2RP #A elim A -A //
#B #A #IHB #IHA @mk_gcr
[ #G #L #T #H
  elim (cp1 … H1RP G L) #s #HK
  lapply (H L (⋆s) T (◊) ? ? ?) -H //
  [ lapply (b2 … IHB G L (◊) … HK) //
  | /3 width=6 by b1, cp3/
  ]
| #G #L #Vs #HVs #T #H1T #H2T #L0 #V0 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0b #T0 #HV0b #HT0 #H destruct
  lapply (b1 … IHB … HB) #HV0
  @(b2 … IHA … (V0 @ V0b))
  /3 width=14 by gcp2_lifts_all, gcp2_lifts, gcp0_lifts, lifts_simple_dx, conj/
| #a #G #L #Vs #U #T #W #HA #L0 #V0 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0b #Y #HV0b #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #U0 #X #HU0 #HX #H destruct
  elim (lifts_inv_bind1 … HX) -HX #W0 #T0 #HW0 #HT0 #H destruct
  @(b3 … IHA … (V0 @ V0b)) /5 width=6 by lifts_applv, lifts_flat, lifts_bind/
| #G #L #Vs #HVs #s #L0 #V0 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0b #Y #HV0b #HY #H destruct
  >(lifts_inv_sort1 … HY) -Y
  lapply (b1 … IHB … HB) #HV0
  @(b4 … IHA … (V0 @ V0b)) /3 width=7 by gcp2_lifts_all, conj/
| #I #G #L #K #Vs #V1 #V2 #i #HA #HV12 #HLK #L0 #V0 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0b #Y #HV0b #HY #H destruct
  elim (lifts_inv_lref1 … HY) -HY #i0 #Hi0 #H destruct
  elim (drops_drop_trans … HL0 … HLK) #X #cs0 #i1 #HL02 #H #Hi1 #Hcs0
  >(at_mono … Hi1 … Hi0) in HL02; -i1 #HL02
  elim (drops_inv_skip2 … Hcs0 … H) -H -cs0 #L2 #W1 #cs0 #Hcs0 #HLK #HVW1 #H destruct
  elim (lift_total W1 0 (i0 + 1)) #W2 #HW12
  elim (lifts_lift_trans  … Hcs0 … HVW1 … HW12) // -Hcs0 -Hi0 #V3 #HV13 #HVW2
  >(lift_mono … HV13 … HV12) in HVW2; -V3 #HVW2
  @(b5 … IHA … (V0 @ V0b) … HW12 HL02) /3 width=5 by lifts_applv/
| #G #L #V1b #V2b #HV12b #a #V #T #HA #HV #L0 #V10 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V10b #Y #HV10b #HY #H destruct
  elim (lifts_inv_bind1 … HY) -HY #V0 #T0 #HV0 #HT0 #H destruct
  elim (lift_total V10 0 1) #V20 #HV120
  elim (liftv_total 0 1 V10b) #V20b #HV120b
  @(b6 … IHA … (V10 @ V10b) (V20 @ V20b)) /3 width=7 by gcp2_lifts, liftv_cons/
  @(HA … (cs + 1)) /2 width=2 by drops_skip/
  [ @lifts_applv //
    elim (liftsv_liftv_trans_le … HV10b … HV120b) -V10b #V10b #HV10b #HV120b
    >(liftv_mono … HV12b … HV10b) -V1b //
  | @(gcr_lift … H1RP … HB … HV120) /2 width=2 by drop_drop/
  ]
| #G #L #Vs #T #W #HA #HW #L0 #V0 #X #cs #HL0 #H #HB
  elim (lifts_inv_applv1 … H) -H #V0b #Y #HV0b #HY #H destruct
  elim (lifts_inv_flat1 … HY) -HY #W0 #T0 #HW0 #HT0 #H destruct
  @(b7 … IHA … (V0 @ V0b)) /3 width=5 by lifts_applv/
]
qed.

lemma acr_abst: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
                ∀a,G,L,W,T,A,B. ⦃G, L, W⦄ ϵ[RP] 〚B〛 → (
                   ∀L0,V0,W0,T0,cs. ⬇*[Ⓕ, cs] L0 ≡ L → ⬆*[cs] W ≡ W0 → ⬆*[cs + 1] T ≡ T0 →
                                   ⦃G, L0, V0⦄ ϵ[RP] 〚B〛 → ⦃G, L0, W0⦄ ϵ[RP] 〚B〛 → ⦃G, L0.ⓓⓝW0.V0, T0⦄ ϵ[RP] 〚A〛
                ) →
                ⦃G, L, ⓛ{a}W.T⦄ ϵ[RP] 〚②B.A〛.
#RR #RS #RP #H1RP #H2RP #a #G #L #W #T #A #B #HW #HA #L0 #V0 #X #cs #HL0 #H #HB
lapply (acr_gcr … H1RP H2RP A) #HCA
lapply (acr_gcr … H1RP H2RP B) #HCB
elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
lapply (gcr_lifts … H1RP … HL0 … HW0 HW) -HW #HW0
lapply (b3 … HCA … a G L0 (◊)) #H @H -H
lapply (b6 … HCA G L0 (◊) (◊) ?) // #H @H -H
[ @(HA … HL0) //
| lapply (b1 … HCB) -HCB #HCB
  lapply (b7 … H2RP G L0 (◊)) /3 width=1 by/
]
qed.

(* Basic_1: removed theorems 2: sc3_arity_gen sc3_repl *)
(* Basic_1: removed local theorems 1: sc3_sn3_abst *)
