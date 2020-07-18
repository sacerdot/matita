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

include "basic_2/rt_transition/cpx_reqg.ma".
include "basic_2/rt_computation/csx_csx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with generic equivalence for local environments ***************)

(* Basic_2A1: uses: csx_lleq_conf *)
lemma csx_reqg_conf (S) (G) (T):
      reflexive … S → symmetric … S →
      ∀L1. ❪G,L1❫ ⊢ ⬈*𝐒 T →
      ∀L2. L1 ≛[S,T] L2 → ❪G,L2❫ ⊢ ⬈*𝐒 T.
#S #G #T #H1S #H2S #L1 #H
@(csx_ind … H) -T #T1 #_ #IH #L2 #HL12
@csx_intro #T2 #HT12 #HnT12
lapply (reqg_cpx_trans … HL12 … HT12) -HT12
/3 width=4 by cpx_reqg_conf_sn/
qed-.

(* Basic_2A1: uses: csx_lleq_trans *)
lemma csx_reqg_trans (S) (G) (T):
      reflexive … S → symmetric … S →
      ∀L1,L2. L1 ≛[S,T] L2 → ❪G,L2❫ ⊢ ⬈*𝐒 T → ❪G,L1❫ ⊢ ⬈*𝐒 T.
/3 width=8 by csx_reqg_conf, reqg_sym/ qed-.
