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

include "basic_2/rt_transition/cpg_lsubr.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with restricted refinement for local environments *************)

lemma lsubr_cpx_trans: ∀h,G. lsub_trans … (cpx h G) lsubr.
#h #G #L1 #T1 #T2 * /3 width=4 by lsubr_cpg_trans, ex_intro/
qed-.

lemma cpx_bind_unit: ∀h,L,G,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                     ∀J,T1,T2. ⦃G, L.ⓤ{J}⦄ ⊢ T1 ⬈[h] T2 →
                     ∀p,I. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈[h] ⓑ{p,I}V2.T2.
/4 width=4 by lsubr_cpx_trans, cpx_bind, lsubr_unit/ qed.

