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

(* Properties with generic extension on referred entries ********************)

(* Basic_2A1: was just: cpr_llpx_sn_conf *)
lemma cpm_lfxs_conf: ∀R,n,h,G. s_r_confluent1 … (cpm n h G) (lfxs R).
/3 width=5 by cpm_fwd_cpx, cpx_lfxs_conf/ qed-.
