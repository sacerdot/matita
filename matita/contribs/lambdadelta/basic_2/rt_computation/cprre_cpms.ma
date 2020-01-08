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
include "basic_2/rt_computation/cprre.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL R-TRANSITION ON TERMS **********)

(* Properties with t-bound rt-computarion on terms **************************)

lemma cpms_cprre_trans (h) (n) (G) (L):
      ∀T1,T0. ❪G,L❫ ⊢T1 ➡*[n,h] T0 →
      ∀T2. ❪G,L❫ ⊢ T0 ➡*[h] 𝐍❪T2❫ → ❪G,L❫ ⊢ T1 ➡*[h,n] 𝐍❪T2❫.
#h #n #G #L #T1 #T0 #HT10 #T2 * #HT02 #HT2
/3 width=3 by cpms_cprs_trans, cpmre_intro/
qed-.
