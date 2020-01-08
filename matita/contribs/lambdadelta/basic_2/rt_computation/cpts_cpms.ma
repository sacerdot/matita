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

include "basic_2/rt_transition/cpt_cpm.ma".
include "basic_2/rt_computation/cpms_cpms.ma".
include "basic_2/rt_computation/cpts.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-COMPUTATION FOR TERMS ***************)

(* Forward lemmas with t-bound rt-computation for terms *********************)

lemma cpts_fwd_cpms (h) (n) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆*[h,n] T2 → ❪G,L❫ ⊢ T1 ➡*[n,h] T2.
#h #n #G #L #T1 #T2 #H
@(cpts_ind_dx … H) -n -T2 [ // ]
#n1 #n2 #T #T2 #_ #IH #HT2
/3 width=3 by cpms_step_dx, cpt_fwd_cpm/
qed-.

lemma cpts_cprs_trans (h) (n) (G) (L) (T):
      ∀T1. ❪G,L❫ ⊢ T1 ⬆*[h,n] T →
      ∀T2. ❪G,L❫ ⊢ T ➡*[h] T2 → ❪G,L❫ ⊢ T1 ➡*[n,h] T2.
#h #n #G #L #T #T1 #HT1 #T2 #HT2
/3 width=3 by cpts_fwd_cpms, cpms_cprs_trans/ qed-.
