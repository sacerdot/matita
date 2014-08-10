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
include "basic_2/computation/gcp_aaa.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR GENERIC REDUCIBILITY ********************)

(* properties concerning lenv refinement for atomic arity assignment ********)

lemma lsuba_lsubc: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
                   ∀G,L1,L2. G ⊢ L1 ⫃⁝ L2 → G ⊢ L1 ⫃[RP] L2.
#RR #RS #RP #H1RP #H2RP #G #L1 #L2 #H elim H -L1 -L2 /2 width=1 by lsubc_pair/
#L1 #L2 #W #V #A #H elim (aaa_inv_cast … H) -H /3 width=4 by acr_aaa, lsubc_beta/
qed.
