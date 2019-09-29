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

include "basic_2/rt_transition/cpg_simple.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with simple terms *********************************************)

(* Basic_2A1: includes: cpr_inv_appl1_simple *)
lemma cpm_inv_appl1_simple: ∀n,h,G,L,V1,T1,U. ⦃G,L⦄ ⊢ ⓐV1.T1 ➡[n,h] U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. ⦃G,L⦄ ⊢ V1 ➡[h] V2 & ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 &
                                     U = ⓐV2.T2.
#n #h #G #L #V1 #T1 #U * #c #Hc #H #HT1 elim (cpg_inv_appl1_simple … H HT1) -H -HT1
#cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct elim (isrt_inv_max … Hc) -Hc
#nV #nT #HnV #HnT #H destruct elim (isrt_inv_shift … HnV) -HnV
#HnV #H destruct /3 width=5 by ex3_2_intro, ex2_intro/
qed-.
