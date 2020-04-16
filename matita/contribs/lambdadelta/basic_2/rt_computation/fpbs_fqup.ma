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

include "static_2/s_computation/fqus_fqup.ma".
include "static_2/static/feqx_fqup.ma".
include "basic_2/rt_computation/fpbs_fqus.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Advanced properties ******************************************************)

lemma teqx_fpbs_trans:
      ∀T1,T. T1 ≛ T →
      ∀G1,G2,L1,L2,T2. ❪G1,L1,T❫ ≥ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by feqx_fpbs_trans, teqx_feqx/ qed-.

lemma fpbs_teqx_trans:
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ ≥ ❪G2,L2,T❫ →
      ∀T2. T ≛ T2 → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fpbs_feqx_trans, teqx_feqx/ qed-.

(* Properties with plus-iterated structural successor for closures **********)

lemma fqup_fpbs:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂+ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/4 width=5 by fqu_fquq, fpbq_fquq, tri_step/
qed.

lemma fpbs_fqup_trans:
      ∀G1,G,L1,L,T1,T. ❪G1,L1,T1❫ ≥ ❪G,L,T❫ →
      ∀G2,L2,T2. ❪G,L,T❫ ⬂+ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fpbs_fqus_trans, fqup_fqus/ qed-.

lemma fqup_fpbs_trans:
      ∀G,G2,L,L2,T,T2. ❪G,L,T❫ ≥ ❪G2,L2,T2❫ →
      ∀G1,L1,T1. ❪G1,L1,T1❫ ⬂+ ❪G,L,T❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fqus_fpbs_trans, fqup_fqus/ qed-.
