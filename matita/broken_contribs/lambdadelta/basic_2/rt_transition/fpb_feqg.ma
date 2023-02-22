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

include "static_2/static/feqg_fqus.ma".
include "static_2/static/feqg_feqg.ma".
include "basic_2/rt_transition/cpx_feqg.ma".
include "basic_2/rt_transition/lpx_reqg.ma".
include "basic_2/rt_transition/fpb.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Propreties with generic equivalence on referred closures *****************)

(* Basic_2A1: includes: fleq_fpbq fpbq_lleq *)
(* Basic_2A1: uses: fpbq_feqx *)
lemma feqg_fpb (S) (G1) (G2) (L1) (L2) (T1) (T2):
      reflexive … S → symmetric … S →
      ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
#S #G1 #G2 #L1 #L2 #T1 #T2 #HS1 #HS2 #H
elim (feqg_inv_gen_sn … H) -H #H #HL12 #HT12 destruct
/4 width=8 by reqg_rpx, teqg_cpx, fpb_intro/
qed.

lemma feqg_fpb_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ≽ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
#S #G #L #T #H1S #H2S #H3S #G1 #L1 #T1 #H1 #G2 #L2 #T2 #H2
elim (fpb_inv_gen … H2) -H2 #L0 #T0 #H0 #HT02 #H
elim (rpx_inv_reqg_lpx S … H) -H // #L3 #HL03 #HL32
elim (feqg_fquq_trans … H1 … H0) -G -L -T // #G #L #T #H1 #H0
lapply (feqg_cpx_trans_cpx … H0 … HT02) // -HT02 #HT2
lapply (feqg_reqg_trans … H0 … HL03) -H0 -HL03 // #H
elim (feqg_inv_gen_sn … H) -H #H #HL3 #_ destruct -T0
/3 width=10 by fpb_intro, reqg_lpx_trans_rpx/
qed-.
