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

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

(* Main propertis ***********************************************************)

axiom aacr_aaa_csubc: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                        ∀L1,T,A. L1 ⊢ T ÷ A →
                        ∀L2. L2 [RP] ⊑ L1 → {L2, T} [RP] ϵ 〚A〛.
(*
#RR #RS #RP #H1RP #H2RP #L1 #T #A #H elim H -L1 -T -A
[ #L #k #L2 #HL2
  lapply (aacr_acr … H1RP H2RP 𝕒) #HAtom
  @(s2 … HAtom … ◊) // /2 width=2/
| * #L #K #V #B #i #HLK #_ #IHB #L2 #HL2
  [
  | lapply (aacr_acr … H1RP H2RP B) #HB
    @(s2 … HB … ◊) //
    @(cp2 … H1RP)
| #L #V #T #B #A #_ #_ #IHB #IHA #L2 #HL2
  lapply (aacr_acr … H1RP H2RP A) #HA
  lapply (aacr_acr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  @(s5 … HA … ◊ ◊) // /3 width=1/
| #L #W #T #B #A #_ #_ #IHB #IHA #L2 #HL2
  lapply (aacr_acr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  @(aacr_abst  … H1RP H2RP) /3 width=1/ -HB /4 width=3/
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
@(s1 … HA) /2 width=4/
qed.
