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

include "static_2/static/feqx.ma".
include "basic_2/rt_computation/cpxs_reqx.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with sort-irrelevant equivalence for closures *****************)

lemma feqx_cpxs_trans: ∀h,G1,G2,L1,L2,T1,T. ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T⦄ →
                       ∀T2. ⦃G2,L2⦄ ⊢ T ⬈*[h] T2 →
                       ∃∃T0. ⦃G1,L1⦄ ⊢ T1 ⬈*[h] T0 & ⦃G1,L1,T0⦄ ≛ ⦃G2,L2,T2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (feqx_inv_gen_dx … H) -H #H #HL12 #HT1 destruct
elim (reqx_cpxs_trans … HT2 … HL12) #T0 #HT0 #HT02
lapply (cpxs_reqx_conf_dx … HT2 … HL12) -HL12 #HL12
elim (teqx_cpxs_trans … HT1 … HT0) -T #T #HT1 #HT0
/4 width=5 by feqx_intro_dx, teqx_trans, ex2_intro/
qed-.
