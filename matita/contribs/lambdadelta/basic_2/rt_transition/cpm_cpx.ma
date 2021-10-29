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

include "basic_2/rt_transition/cpx.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Forward lemmas with extended context-sensitive rt-transition for terms ***)

(* Basic_2A1: includes: cpr_cpx *)
lemma cpm_fwd_cpx (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 → ❨G,L❩ ⊢ T1 ⬈ T2.
#h #n #G #L #T1 #T2 * #c #_ #HT12
/2 width=4 by cpg_cpx/
qed-.
