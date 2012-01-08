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

include "Basic_2/static/aaa.ma".
include "Basic_2/computation/lsubc.ma".
(*
axiom lsubc_ldrops_trans: ∀RP,L1,L2. L1 [RP] ⊑ L2 → ∀K2,des. ⇩[des] L2 ≡ K2 →
                          ∃∃K1. ⇩[des] L1 ≡ K1 & K1 [RP] ⊑ K2.
*)
axiom ldrops_lsubc_trans: ∀RP,L1,K1,des. ⇩*[des] L1 ≡ K1 → ∀K2. K1 [RP] ⊑ K2 →
                          ∃∃L2. L1 [RP] ⊑ L2 & ⇩*[des] L2 ≡ K2.

axiom lifts_trans: ∀T1,T,des1. ⇧*[des1] T1 ≡ T → ∀T2:term. ∀des2. ⇧*[des2] T ≡ T2 →
                   ⇧*[des1 @ des2] T1 ≡ T2.

axiom ldrops_trans: ∀L1,L,des1. ⇩*[des1] L1 ≡ L → ∀L2,des2. ⇩*[des2] L ≡ L2 →
                    ⇩*[des2 @ des1] L1 ≡ L2.

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

(* Main propertis ***********************************************************)

axiom aacr_aaa_csubc_lifts: ∀RR,RS,RP. 
                              acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                              ∀L1,T,A. L1 ⊢ T ÷ A → ∀L0,des. ⇩*[des] L0 ≡ L1 →
                              ∀T0. ⇧*[des] T ≡ T0 → ∀L2. L2 [RP] ⊑ L0 →
                              ⦃L2, T0⦄ [RP] ϵ 〚A〛.
(*
#RR #RS #RP #H1RP #H2RP #L1 #T #A #H elim H -L1 -T -A
[ (*#L #k #L2 #HL2
  lapply (aacr_acr … H1RP H2RP 𝕒) #HAtom
  @(s2 … HAtom … ◊) // /2 width=2/ *)
| (* * #L #K #V #B #i #HLK #_ #IHB #L2 #HL2
  [
  | lapply (aacr_acr … H1RP H2RP B) #HB
    @(s2 … HB … ◊) //
(*    @(cp2 … H1RP) *)
  ] *)
| (* #L #V #T #B #A #_ #_ #IHB #IHA #L2 #HL2
  lapply (aacr_acr … H1RP H2RP A) #HA
  lapply (aacr_acr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  @(s5 … HA … ◊ ◊) // /3 width=1/ *)
| #L #W #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL02
  elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
  @(aacr_abst  … H1RP H2RP)
  [ lapply (aacr_acr … H1RP H2RP B) #HB
    @(s1 … HB) /2 width=5/
  | #L3 #V3 #T3 #des3 #HL32 #HT03 #HB
    elim (lifts_total des3 W0) #W2 #HW02
    elim (ldrops_lsubc_trans … HL32 … HL02) -L2 #L2 #HL32 #HL20
    @(IHA (L2. 𝕓{Abst} W2) … (ss des @ ss des3))
    /2 width=3/ /3 width=5/ /4 width=6/
  ]
| /3 width=1/
| #L #V #T #A #_ #_ #IH1A #IH2A #L2 #HL2
  lapply (aacr_acr … H1RP H2RP A) #HA
  lapply (s1 … HA) #H
  @(s6 … HA … ◊) /2 width=1/ /3 width=1/
]
*)
lemma acp_aaa: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
               ∀L,T,A. L ⊢ T ÷ A → RP L T.
#RR #RS #RP #H1RP #H2RP #L #T #A #HT
lapply (aacr_acr … H1RP H2RP A) #HA
@(s1 … HA) /2 width=8/
qed.
