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

include "basic_2/rt_transition/cnr.ma".
include "basic_2/rt_computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Inversion lemmas with normal terms for r-transition **********************)

(* Basic_1: was: nf2_pr3_unfold *)
(* Basic_2A1: was: cprs_inv_cnr1 *)
lemma cprs_inv_cnr_sn (h) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 → ❪G,L❫ ⊢ ➡𝐍[h,0] T1 → T1 = T2.
#h #G #L #T1 #T2 #H @(cprs_ind_sn … H) -T1 //
#T1 #T0 #HT10 #_ #IH #HT1
lapply (HT1 … HT10) -HT10 #H destruct /2 width=1 by/
qed-.
