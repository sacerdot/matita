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

include "basic_2/rt_transition/cpx_lfxs.ma".
include "basic_2/rt_transition/cpm_cpx.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Properties with context-sensitive free variables *************************)

lemma cpm_fle_comp: ∀n,h,G. R_fle_compatible (cpm n h G).
/3 width=6 by cpm_fwd_cpx, cpx_fle_comp/ qed-.

lemma lfpr_fle_comp: ∀h,G. lfxs_fle_compatible (cpm 0 h G).
/4 width=5 by cpm_fwd_cpx, lfpx_fle_comp, lfxs_co/ qed-.

(* Properties with generic extension on referred entries ********************)

(* Basic_2A1: was just: cpr_llpx_sn_conf *)
lemma cpm_lfxs_conf: ∀R,n,h,G. s_r_confluent1 … (cpm n h G) (lfxs R).
/3 width=5 by cpm_fwd_cpx, cpx_lfxs_conf/ qed-.
