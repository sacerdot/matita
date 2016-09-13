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

(* Forward lemmas with uncounted context-sensitive rt-transition for terms **)

(* Basic_2A1: includes: cpr_cpx *)
lemma cpm_fwd_cpx: ∀n,h,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2 → ⦃G, L⦄ ⊢ T1 ⬈[h] T2.
#n #h #G #L #T1 #T2 * #c #Hc #H elim H -L -T1 -T2
/2 width=3 by cpx_theta, cpx_beta, cpx_ee, cpx_eps, cpx_zeta, cpx_flat, cpx_bind, cpx_lref, cpx_delta/
qed-.
