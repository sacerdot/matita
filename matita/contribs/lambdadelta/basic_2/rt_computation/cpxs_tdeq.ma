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

include "basic_2/syntax/tdeq_tdeq.ma".
include "basic_2/rt_computation/cpxs.ma".
include "basic_2/rt_transition/cpx_lfdeq.ma".
include "basic_2/rt_transition/lfpx_fqup.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS ************)

lemma tdeq_cpxs_trans: ∀h,o,U1,T1. U1 ≡[h, o] T1 → ∀G,L,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → 
                       ∃∃U2.  ⦃G, L⦄ ⊢ U1 ⬈*[h] U2 & U2 ≡[h, o] T2.
#h #o #U1 #T1 #HUT1 #G #L #T2 #HT12 @(cpxs_ind … HT12) -T2 /2 width=3 by ex2_intro/
#T #T2 #_ #HT2 * #U #HU1 #HUT elim (tdeq_cpx_trans … HUT … HT2) -T -T1
/3 width=3 by ex2_intro, cpxs_strap1/
qed-.

(* Note: this requires tdeq to be symmetric *)
lemma cpxs_tdneq_inv_step_sn: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬈*[h] T2 → (T1 ≡[h, o] T2 → ⊥) →
                              ∃∃T,T0. ⦃G, L⦄ ⊢ T1 ⬈[h] T & T1 ≡[h, o] T → ⊥ & ⦃G, L⦄ ⊢ T ⬈*[h] T0 & T0 ≡[h, o] T2.
#h #o #G #L #T1 #T2 #H @(cpxs_ind_dx … H) -T1
[ #H elim H -H //
| #T1 #T #H1 #H2 #IH #Hn12 elim (tdeq_dec h o T1 T) #H destruct
  [ -H1 -H2 elim IH -IH /3 width=3 by tdeq_trans/ -Hn12
    #X #X2 #HTX #HnTX #HX2 #HXT2 elim (tdeq_cpx_trans … H … HTX) -HTX
    #X1 #HTX1 #HX1 elim (tdeq_cpxs_trans … HX1 … HX2) -HX2
    /5 width=8 by tdeq_canc_sn, tdeq_trans, ex4_2_intro/ (* Note: 2 tdeq_trans *)
  | -IH -Hn12 /3 width=6 by ex4_2_intro/
  ]
]
qed-.

(* Basic_2A1: removed theorems 1: cpxs_neq_inv_step_sn *)
