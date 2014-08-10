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

include "basic_2/grammar/genv.ma".
include "basic_2/multiple/drops.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

definition candidate: Type[0] ≝ relation3 genv lenv term.

definition CP0 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L0,L,T,T0,s,d,e. NF … (RR G L) RS T →
                 ⇩[s, d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → NF … (RR G L0) RS T0.

definition CP0s ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                  ∀G,L0,L,s,des. ⇩*[s, des] L0 ≡ L →
                  ∀T,T0. ⇧*[des] T ≡ T0 →
                  NF … (RR G L) RS T → NF … (RR G L0) RS T0.

definition CP1 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L. ∃k. NF … (RR G L) RS (⋆k).

definition CP2 ≝ λRP:candidate.
                 ∀G,L,T,k. RP G L (ⓐ⋆k.T) → RP G L T.

(* requirements for generic computation properties *)
record gcp (RR:relation4 genv lenv term term) (RS:relation term) (RP:candidate) : Prop ≝
{ cp0: CP0 RR RS;
  cp1: CP1 RR RS;
  cp2: CP2 RP
}.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_lift1 *)
lemma gcp_lifts: ∀RR,RS. CP0 RR RS → CP0s RR RS.
#RR #RS #HRR #G #L1 #L2 #s #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=10 by/
]
qed.
