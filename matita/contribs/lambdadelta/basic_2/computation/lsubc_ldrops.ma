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

include "basic_2/computation/lsubc_ldrop.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

(* Properties concerning generic local environment slicing ******************)

(* Basic_1: was: csubc_drop1_conf_rev *)
lemma ldrops_lsubc_trans: ∀RR,RS,RP.
                          acp RR RS RP → acr RR RS RP (λG,L,T. RP G L T) →
                          ∀G,L1,K1,des. ⇩*[Ⓕ, des] L1 ≡ K1 → ∀K2. G ⊢ K1 ⫃[RP] K2 →
                          ∃∃L2. G ⊢ L1 ⫃[RP] L2 & ⇩*[Ⓕ, des] L2 ≡ K2.
#RR #RS #RP #Hacp #Hacr #G #L1 #K1 #des #H elim H -L1 -K1 -des
[ /2 width=3 by ldrops_nil, ex2_intro/
| #L1 #L #K1 #des #d #e #_ #HLK1 #IHL #K2 #HK12
  elim (ldrop_lsubc_trans … Hacp Hacr … HLK1 … HK12) -Hacp -Hacr -K1 #K #HLK #HK2
  elim (IHL … HLK) -IHL -HLK /3 width=5 by ldrops_cons, ex2_intro/
]
qed-.
