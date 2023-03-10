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

include "basic_2A/computation/lsubc_drop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR GENERIC REDUCIBILITY ********************)

(* Properties concerning generic local environment slicing ******************)

(* Basic_1: was: csubc_drop1_conf_rev *)
lemma drops_lsubc_trans: ∀RR,RS,RP. gcp RR RS RP →
                         ∀G,L1,K1,cs. ⬇*[Ⓕ, cs] L1 ≡ K1 → ∀K2. G ⊢ K1 ⫃[RP] K2 →
                         ∃∃L2. G ⊢ L1 ⫃[RP] L2 & ⬇*[Ⓕ, cs] L2 ≡ K2.
#RR #RS #RP #Hgcp #G #L1 #K1 #cs #H elim H -L1 -K1 -cs
[ /2 width=3 by drops_nil, ex2_intro/
| #L1 #L #K1 #cs #l #m #_ #HLK1 #IHL #K2 #HK12
  elim (drop_lsubc_trans … Hgcp … HLK1 … HK12) -Hgcp -K1 #K #HLK #HK2
  elim (IHL … HLK) -IHL -HLK /3 width=5 by drops_cons, ex2_intro/
]
qed-.
