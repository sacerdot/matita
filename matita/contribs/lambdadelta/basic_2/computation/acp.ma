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
include "basic_2/substitution/ldrops.ma".

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

definition CP1 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L. ∃k. NF … (RR G L) RS (⋆k).

definition CP2 ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                 ∀G,L0,L,T,T0,s,d,e. NF … (RR G L) RS T →
                 ⇩[s, d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → NF … (RR G L0) RS T0.

definition CP2s ≝ λRR:relation4 genv lenv term term. λRS:relation term.
                  ∀G,L0,L,s,des. ⇩*[s, des] L0 ≡ L →
                  ∀T,T0. ⇧*[des] T ≡ T0 →
                  NF … (RR G L) RS T → NF … (RR G L0) RS T0.

definition CP3 ≝ λRP:relation3 genv lenv term.
                 ∀G,L,T,k. RP G L (ⓐ⋆k.T) → RP G L T.

definition CP4 ≝ λRP:relation3 genv lenv term.
                 ∀G,L,W,T. RP G L W → RP G L T → RP G L (ⓝW.T).

(* requirements for abstract computation properties *)
record acp (RR:relation4 genv lenv term term) (RS:relation term) (RP:relation3 genv lenv term) : Prop ≝
{ cp1: CP1 RR RS;
  cp2: CP2 RR RS;
  cp3: CP3 RP;
  cp4: CP4 RP
}.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_lift1 *)
lemma acp_lifts: ∀RR,RS. CP2 RR RS → CP2s RR RS.
#RR #RS #HRR #G #L1 #L2 #s #des #H elim H -L1 -L2 -des
[ #L #T1 #T2 #H #HT1
  <(lifts_inv_nil … H) -H //
| #L1 #L #L2 #des #d #e #_ #HL2 #IHL #T2 #T1 #H #HLT2
  elim (lifts_inv_cons … H) -H /3 width=10 by/
]
qed.
