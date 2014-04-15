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

include "basic_2/computation/cpxs_llpx.ma".
include "basic_2/computation/csx_alt.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Properties on lazy sn extended reduction for local environments **********)

lemma csx_llpx_conf: ∀h,g,G,L1,T. ⦃G, L1⦄ ⊢ ⬊*[h, g] T →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡[h, g, T, 0] L2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #T #H @(csx_ind_alt … H) -T
/5 width=3 by csx_intro_cpxs, llpx_cpxs_trans, cpxs_llpx_conf/ (* 2 cpxs_llpx_trans *)
qed-.
