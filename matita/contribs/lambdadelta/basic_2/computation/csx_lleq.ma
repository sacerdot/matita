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

include "basic_2/reduction/cpx_lleq.ma".
include "basic_2/computation/csx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Properties on lazy equivalence for local environments ********************)

lemma csx_lleq_conf: ∀h,g,G,L1,T. ⦃G, L1⦄ ⊢ ⬊*[h, g] T →
                     ∀L2. L1 ≡[T, 0] L2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #T #H @(csx_ind … H) -T
/4 width=6 by csx_intro, cpx_lleq_conf_dx, lleq_cpx_trans/
qed-.

lemma csx_lleq_trans: ∀h,g,G,L1,L2,T.
                      L1 ≡[T, 0] L2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T → ⦃G, L1⦄ ⊢ ⬊*[h, g] T.
/3 width=3 by csx_lleq_conf, lleq_sym/ qed-.
