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

include "basic_2/reducibility/fpr_fpr.ma".
include "basic_2/computation/fprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON CLOSURES ****************************)

(* Advanced properties ******************************************************)

lemma fprs_strip: ∀L0,L1,T0,T1. ⦃L0, T0⦄ ➡ ⦃L1, T1⦄ →
                  ∀L2,T2. ⦃L0, T0⦄ ➡* ⦃L2, T2⦄ →
                  ∃∃L,T. ⦃L1, T1⦄ ➡* ⦃L, T⦄ & ⦃L2, T2⦄ ➡ ⦃L, T⦄.
#H1 #H2 #H3 #H4 #H5 #H6 #H7 #H8
/2 width=4/ qed.

(* Main propertis ***********************************************************)

theorem fprs_conf: bi_confluent … fprs.
/2 width=4/ qed.

theorem fprs_trans: bi_transitive … fprs.
/2 width=4/ qed.
