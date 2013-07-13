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

include "basic_2/substitution/ldrops.ma".

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

definition CP1 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L. ∃k. NF … (RR L) RS (⋆k).

definition CP2 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L0,L,T,T0,d,e. NF … (RR L) RS T →
                 ⇩[d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → NF … (RR L0) RS T0.

definition CP2s ≝ λRR:lenv→relation term. λRS:relation term.
                  ∀L0,L,des. ⇩*[des] L0 ≡ L →
                  ∀T,T0. ⇧*[des] T ≡ T0 →
                  NF … (RR L) RS T → NF … (RR L0) RS T0.

definition CP3 ≝ λRP:lenv→predicate term.
                 ∀L,V,k. RP L (ⓐ⋆k.V) → RP L V.

(* requirements for abstract computation properties *)
record acp (RR:lenv->relation term) (RS:relation term) (RP:lenv→predicate term) : Prop ≝
{ cp1: CP1 RR RS;
  cp2: CP2 RR RS;
  cp3: CP3 RP
}.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_lift1 *)
lemma acp_lifts: ∀RR,RS. CP2 RR RS → CP2s RR RS.
#RR #RS #HRR #L1 #L2 #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=9/
]
qed.
