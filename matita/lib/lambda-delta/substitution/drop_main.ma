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

include "lambda-delta/substitution/drop_defs.ma".

(* DROPPING *****************************************************************)

(* the main properties ******************************************************)

axiom drop_conf_ge: ∀d1,e1,L,L1. ↑[d1, e1] L1 ≡ L →
                    ∀e2,L2. ↑[0, e2] L2 ≡ L → d1 + e1 ≤ e2 →
                    ↑[0, e2 - e1] L2 ≡ L1.

axiom drop_conf_lt: ∀d1,e1,L,L1. ↑[d1, e1] L1 ≡ L →
                    ∀e2,K2,I,V2. ↑[0, e2] K2. 𝕓{I} V2 ≡ L →
                    e2 < d1 → let d ≝ d1 - e2 - 1 in
                    ∃∃K1,V1. ↑[0, e2] K1. 𝕓{I} V1 ≡ L1 & 
                             ↑[d, e1] K2 ≡ K1 & ↑[d,e1] V1 ≡ V2.

axiom drop_trans_le: ∀d1,e1,L1. ∀L:lenv. ↑[d1, e1] L ≡ L1 →
                     ∀e2,L2. ↑[0, e2] L2 ≡ L → e2 ≤ d1 →
                     ∃∃L0. ↑[0, e2] L0 ≡ L1 & ↑[d1 - e2, e1] L2 ≡ L0.

axiom drop_trans_ge: ∀d1,e1,L1,L. ↑[d1, e1] L ≡ L1 →
                     ∀e2,L2. ↑[0, e2] L2 ≡ L → d1 ≤ e2 → ↑[0, e1 + e2] L2 ≡ L1.
