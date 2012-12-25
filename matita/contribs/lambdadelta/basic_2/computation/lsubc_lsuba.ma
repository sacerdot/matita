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

include "basic_2/static/lsuba.ma".
include "basic_2/computation/acp_aaa.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

(* properties concerning lenv refinement for atomic arity assignment ********)

lemma lsubc_lsuba: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                   ∀L1,L2. L1 ⁝⊑ L2 → L1 ⊑[RP] L2.
#RR #RS #RP #H1RP #H2RP #L1 #L2 #H elim H -L1 -L2
// /2 width=1/ /3 width=4/
qed.
