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

include "basic_2/reducibility/ltpr_ltpr.ma".
include "basic_2/computation/ltprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ******************)

(* Advanced properties ******************************************************)

lemma ltprs_strip: ∀L1. ∀L:lenv. L ➡* L1 → ∀L2. L ➡ L2 →
                   ∃∃L0. L1 ➡ L0 & L2 ➡* L0.
/3 width=3/ qed.

(* Main properties **********************************************************)

theorem ltprs_conf: confluent … ltprs.
/3 width=3/ qed.

theorem ltprs_trans: Transitive … ltprs.
/2 width=3/ qed.
