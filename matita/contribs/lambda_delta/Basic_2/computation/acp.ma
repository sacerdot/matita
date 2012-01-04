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

include "Basic_2/unfold/ldrops.ma".

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

definition CP1 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L,k. NF … (RR L) RS (⋆k).

definition CP2 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L,K,W,i. ⇓[0,i] L ≡ K. 𝕓{Abst} W → NF … (RR L) RS (#i).

definition CP3 ≝ λRR:lenv→relation term. λRP:lenv→predicate term.
                 ∀L,V,k. RP L (𝕔{Appl}⋆k.V) → RP L V.

definition CP4 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L0,L,T,T0,d,e. NF … (RR L) RS T → 
                 ⇓[d,e] L0 ≡ L → ⇑[d, e] T ≡ T0 → NF … (RR L0) RS T0.

definition CP4s ≝ λRR:lenv→relation term. λRS:relation term.
                  ∀L0,L,des. ⇓[des] L0 ≡ L →
                  ∀T,T0. ⇑[des] T ≡ T0 →
                  NF … (RR L) RS T → NF … (RR L0) RS T0.

(* requirements for abstract computation properties *)
record acp (RR:lenv->relation term) (RS:relation term) (RP:lenv→predicate term) : Prop ≝
{ cp1: CP1 RR RS;
  cp2: CP2 RR RS;
  cp3: CP3 RR RP;
  cp4: CP4 RR RS
}.

(* Basic properties *********************************************************)

lemma acp_lifts: ∀RR,RS. CP4 RR RS → CP4s RR RS.
#RR #RS #HRR #L1 #L2 #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=9/
]
qed.
