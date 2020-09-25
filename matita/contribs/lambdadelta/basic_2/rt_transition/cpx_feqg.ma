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

include "static_2/static/feqg.ma".
include "basic_2/rt_transition/cpx_reqg.ma".
include "basic_2/rt_transition/rpx_reqg.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Properties with generic equivalence for closures *************************)

lemma feqg_cpx_trans_cpx (S):
      reflexive … S → symmetric … S →
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T❫ →
      ∀T2. ❪G2,L2❫ ⊢ T ⬈ T2 → ❪G1,L1❫ ⊢ T1 ⬈ T2.
#S #H1S #H2S #G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (feqg_inv_gen_dx … H) -H // #H #HL12 #HT1 destruct
@(cpx_teqg_repl_reqg … HT2)
/2 width=7 by reqg_sym, teqg_sym, teqg_refl/
qed-.

lemma feqg_cpx_trans_feqg (S):
      reflexive … S → symmetric … S →
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T❫ →
      ∀T2. ❪G2,L2❫ ⊢ T ⬈ T2 → ❪G1,L1,T2❫ ≛[S] ❪G2,L2,T2❫.
#S #H1S #H2S #G1 #G2 #L1 #L2 #T1 #T #H #T2 #HT2
elim (feqg_inv_gen_dx … H) -H // #H #HL12 #_ destruct
lapply (cpx_reqg_conf_dx … HT2 … HL12) -HT2 -HL12 // #HL12
/3 width=1 by feqg_intro_sn, teqg_refl/
qed-.
