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

include "basic_2/computation/fpbs.ma".
include "basic_2/computation/csx_lleq.ma".
include "basic_2/computation/csx_lpx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Advanced properties ******************************************************)

lemma csx_fpb_conf: ∀h,g,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                    ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #L1 #T1 #HT1 #G2 #L2 #T2 *
/2 width=5 by csx_cpx_trans, csx_fquq_conf, csx_lpx_conf, csx_lleq_conf/
qed-.

lemma csx_fpbs_conf: ∀h,g,G1,L1,T1. ⦃G1, L1⦄ ⊢ ⬊*[h, g] T1 →
                     ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G2, L2⦄ ⊢ ⬊*[h, g] T2.
#h #g #G1 #L1 #T1 #HT1 #G2 #L2 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
/2 width=5 by csx_fpb_conf/
qed-.
