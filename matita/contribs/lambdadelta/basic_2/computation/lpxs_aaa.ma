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

include "basic_2/reduction/lpx_aaa.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Properties about atomic arity assignment on terms ************************)

lemma lpxs_aaa_conf: ∀h,g,G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → ⦃G, L2⦄ ⊢ T ⁝ A.
#h #g #G #L1 #T #A #HT #L2 #HL12
@(TC_Conf3 … (λL,A. ⦃G, L⦄ ⊢ T ⁝ A) … HT ? HL12) /2 width=5 by lpx_aaa_conf/
qed-.

lemma lprs_aaa_conf: ∀G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L2⦄ ⊢ T ⁝ A.
/3 width=5 by lprs_lpxs, lpxs_aaa_conf/ qed-.
