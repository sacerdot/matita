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
include "Basic_2/grammar/term_simple.ma".
include "Basic_2/substitution/lift_vector.ma".
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
| APair B A ⇒ ∀V. aacr RP B L V → aacr RP A L (𝕔{Appl} V. T)
].

interpretation
   "candidate of reducibility of an atomic arity (abstract)"
   'InEInt RP L T A = (aacr RP A L T).

(* Basic properties *********************************************************)

axiom aacr_acr: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                ∀A. acr RR RS RP (aacr RP A).
(*
#RR #RS #RP #H1RP #H2RP #A elim A -A normalize //
#B #A #IHB #IHA @mk_acr normalize
[ #L #T #H
  lapply (H (⋆0) ?) -H [ @(s2 … IHB … ◊) // /2 width=2/ ] #H
  @(cp3 … H1RP … 0) @(s1 … IHA) //
| #L #Vs #HVs #T #H1T #H2T #V #HB
  lapply (s1 … IHB … HB) #HV
  @(s2 … IHA … (V :: Vs)) // /2 width=1/
| #L #Vs #V #T #W #HA #HW #V0 #HB
  @(s3 … IHA … (V0 :: Vs)) // /2 width=1/
| #L #V1s #V2s #HV12s #V #T #HA #HV #V1 #HB
  elim (lift_total V1 0 1) #V2 #HV12
  @(s5 … IHA … (V1 :: V1s) (V2 :: V2s)) // /2 width=1/
  @HA @(s7 … IHB … HB … HV12) /2 width=1/
| #L #Vs #T #W #HA #HW #V0 #HB
  @(s6 … IHA … (V0 :: Vs)) // /2 width=1/
| #L1 #L2 #T1 #T2 #d #e #HA #HL21 #HT12 #V2 #HB
  @(s7 … IHA … HL21) [2: @HA [2: 
]
qed.
*)
lemma aacr_abst: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                 ∀L,W,T,A,B. RP L W →
                 (∀V. ⦃L, V⦄ [RP] ϵ 〚B〛 → ⦃L. 𝕓{Abbr}V, T⦄ [RP] ϵ 〚A〛) →
                              ⦃L, 𝕓{Abst}W. T⦄ [RP] ϵ 〚𝕔B. A〛.
#RR #RS #RP #H1RP #H2RP #L #W #T #A #B #HW #HA #V #HB
lapply (aacr_acr … H1RP H2RP A) #HCA
lapply (aacr_acr … H1RP H2RP B) #HCB
lapply (s1 … HCB) -HCB #HCB
@(s3 … HCA … ◊) // @(s5 … HCA … ◊ ◊) // /2 width=1/
qed.
