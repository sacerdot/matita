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

include "basic_2/rt_transition/rpx_fsle.ma".
include "basic_2/rt_transition/cpm_cpx.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Forward lemmas with free variables inclusion for restricted closures *****)

lemma cpm_fsge_comp (h) (n) (G):
      R_fsge_compatible (λL. cpm h G L n).
/3 width=6 by cpm_fwd_cpx, cpx_fsge_comp/ qed-.

lemma rpr_fsge_comp (h) (G):
      rex_fsge_compatible (λL. cpm h G L 0).
/4 width=5 by cpm_fwd_cpx, rpx_fsge_comp, rex_co/ qed-.

(* Properties with generic extension on referred entries ********************)

(* Basic_2A1: was just: cpr_llpx_sn_conf *)
lemma cpm_rex_conf_sn (R) (h) (n) (G):
      s_r_confluent1 … (λL. cpm h G L n) (rex R).
/3 width=5 by cpm_fwd_cpx, cpx_rex_conf_sn/ qed-.
