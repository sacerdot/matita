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

lemma aaa_lpxs_conf: ∀h,g,L1,T,A.
                     L1 ⊢ T ⁝ A → ∀L2. ⦃h, L1⦄ ⊢ ➡*[h, g] L2 → L2 ⊢ T ⁝ A.
#h #g #L1 #T #A #HT #L2 #HL12
@(TC_Conf3 … (λL,A. ⦃G, L⦄ ⊢ T ⁝ A) … HT ? HL12) /2 width=5 by aaa_lpx_conf/
qed-.

lemma aaa_lprs_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ⊢ ➡* L2 → L2 ⊢ T ⁝ A.
#L1 #T #A #HT #L2 #HL12
@(aaa_lpxs_conf … HT) -A -T /2 width=3/
qed-.
