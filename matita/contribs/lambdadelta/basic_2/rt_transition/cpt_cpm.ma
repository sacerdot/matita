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

include "basic_2/rt_transition/cpm.ma".
include "basic_2/rt_transition/cpt_fqu.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

(* Forward lemmas with t-bound rt-transition for terms **********************)

lemma cpt_fwd_cpm (h) (n) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬆[h,n] T2 → ❪G,L❫ ⊢ T1 ➡[n,h] T2.
#h #n #G #L #T1 #T2 #H
@(cpt_ind … H) -n -G -L -T1 -T2
/3 width=3 by cpm_ee, cpm_cast, cpm_appl, cpm_bind, cpm_lref, cpm_ell, cpm_delta/
qed-.
