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

include "basic_2/rt_transition/lfpx_frees.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with generic extension on referred entries ********************)

(* Note: lemma 1000 *)
(* Basic_2A1: was just: cpx_llpx_sn_conf *)
lemma cpx_lfxs_conf: ∀R,h,G. s_r_confluent1 … (cpx h G) (lfxs R).
#R #h #G #L1 #T1 #T2 #H #L2 * #f1 #Hf1 elim (cpx_frees_conf … Hf1 … H) -T1
/3 width=5 by sle_lexs_trans, ex2_intro/
qed-.
