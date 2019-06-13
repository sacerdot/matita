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

include "basic_2/rt_computation/cpms_cpms.ma".
include "basic_2/rt_computation/cprs_cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Main properties **********************************************************)

(* Basic_1: was: pr3_t *)
(* Basic_1: includes: pr1_t *)
theorem cprs_trans (h) (G) (L): Transitive … (cpms h G L 0).
/2 width=3 by cpms_trans/ qed-.

(* Basic_1: was: pr3_confluence *)
(* Basic_1: includes: pr1_confluence *)
theorem cprs_conf (h) (G) (L): confluent2 … (cpms h G L 0) (cpms h G L 0).
#h #G #L #T0 #T1 #HT01 #T2 #HT02
elim (TC_confluent2 … T0 T1 … T2)
[ /3 width=3 by cprs_CTC, ex2_intro/ |5,6: skip
| /2 width=1 by cprs_inv_CTC/
| /2 width=1 by cprs_inv_CTC/
| /2 width=3 by cpr_conf/
]
qed-.

(* Basic_1: was: pr3_flat *)
theorem cprs_flat (h) (G) (L):
                  ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[h] T2 →
                  ∀V1,V2. ⦃G,L⦄ ⊢ V1 ➡*[h] V2 →
                  ∀I. ⦃G,L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h] ⓕ{I}V2.T2.
#h #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind_dx … H) -V2
[ /2 width=3 by cprs_flat_dx/
| /3 width=3 by cpr_pair_sn, cprs_step_dx/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr3_gen_appl *)
(* Basic_2A1: was: cprs_inv_appl1 *)
lemma cprs_inv_appl_sn (h) (G) (L):
                       ∀V1,T1,X2. ⦃G,L⦄ ⊢ ⓐV1.T1 ➡*[h] X2 →
                       ∨∨ ∃∃V2,T2.       ⦃G,L⦄ ⊢ V1 ➡*[h] V2 &
                                         ⦃G,L⦄ ⊢ T1 ➡*[h] T2 &
                                         X2 = ⓐV2. T2
                        | ∃∃p,W,T.       ⦃G,L⦄ ⊢ T1 ➡*[h] ⓛ{p}W.T &
                                         ⦃G,L⦄ ⊢ ⓓ{p}ⓝW.V1.T ➡*[h] X2
                        | ∃∃p,V0,V2,V,T. ⦃G,L⦄ ⊢ V1 ➡*[h] V0 & ⬆*[1] V0 ≘ V2 &
                                         ⦃G,L⦄ ⊢ T1 ➡*[h] ⓓ{p}V.T &
                                         ⦃G,L⦄ ⊢ ⓓ{p}V.ⓐV2.T ➡*[h] X2.
#h #G #L #V1 #T1 #X2 #H elim (cpms_inv_appl_sn … H) -H *
[ /3 width=5 by or3_intro0, ex3_2_intro/
| #n1 #n2 #p #V2 #T2 #HT12 #HTX2 #H
  elim (plus_inv_O3 … H) -H #H1 #H2 destruct
  /3 width=5 by or3_intro1, ex2_3_intro/
| #n1 #n2 #p #V2 #W2 #V #T2 #HV12 #HVW2 #HT12 #HTX2 #H
  elim (plus_inv_O3 … H) -H #H1 #H2 destruct
  /3 width=9 by or3_intro2, ex4_5_intro/
]
qed-.
