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

include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_computation/cpxs.ma".
include "basic_2/rt_computation/cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Forward lemmas with extended context-sensitive rt-computation for terms **)

(* Basic_2A1: includes: scpds_fwd_cpxs cprs_cpxs *)
lemma cpms_fwd_cpxs (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡*[h,n] T2 → ❨G,L❩ ⊢ T1 ⬈* T2.
#h #n #G #L #T1 #T2 #H @(cpms_ind_dx … H) -T2
/3 width=5 by cpxs_strap1, cpm_fwd_cpx/
qed-.
