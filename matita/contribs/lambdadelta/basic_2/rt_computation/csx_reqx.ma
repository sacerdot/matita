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

include "basic_2/rt_transition/cpx_reqx.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with sort-irrelevant equivalence for local environments *******)

(* Basic_2A1: uses: csx_lleq_conf *)
lemma csx_reqx_conf: ∀h,G,L1,T. ❪G,L1❫ ⊢ ⬈*[h] 𝐒❪T❫ →
                     ∀L2. L1 ≛[T] L2 → ❪G,L2❫ ⊢ ⬈*[h] 𝐒❪T❫.
#h #G #L1 #T #H
@(csx_ind … H) -T #T1 #_ #IH #L2 #HL12
@csx_intro #T2 #HT12 #HnT12
elim (reqx_cpx_trans … HL12 … HT12) -HT12
/5 width=5 by cpx_reqx_conf_sn, csx_teqx_trans, teqx_trans/
qed-.

(* Basic_2A1: uses: csx_lleq_conf *)
lemma csx_reqx_trans: ∀h,L1,L2,T. L1 ≛[T] L2 →
                      ∀G. ❪G,L2❫ ⊢ ⬈*[h] 𝐒❪T❫ → ❪G,L1❫ ⊢ ⬈*[h] 𝐒❪T❫.
/3 width=3 by csx_reqx_conf, reqx_sym/ qed-.
