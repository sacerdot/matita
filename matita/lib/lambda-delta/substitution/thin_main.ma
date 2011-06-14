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

include "lambda-delta/substitution/thin_defs.ma".

(* THINNING *****************************************************************)

(* the main properties ******************************************************)

axiom thin_conf_ge: ∀d1,e1,L,L1. ↓[d1,e1] L ≡ L1 →
                    ∀e2,L2. ↓[0,e2] L ≡ L2 → d1 + e1 ≤ e2 → ↓[0,e2-e1] L1 ≡ L2.

axiom thin_conf_lt: ∀d1,e1,L,L1. ↓[d1,e1] L ≡ L1 →
                    ∀e2,K2,I,V2. ↓[0,e2] L ≡ K2. 𝕓{I} V2 →
                    e2 < d1 → let d ≝ d1 - e2 - 1 in
                    ∃∃K1,V1. ↓[0,e2] L1 ≡ K1. 𝕓{I} V1 & ↓[d,e1] K2 ≡ K1 & ↑[d,e1] V1 ≡ V2.

axiom thin_trans_le: ∀d1,e1,L1,L. ↓[d1, e1] L1 ≡ L →
                     ∀e2,L2. ↓[0, e2] L ≡ L2 → e2 ≤ d1 →
                     ∃∃L0. ↓[0, e2] L1 ≡ L0 & ↓[d1 - e2, e1] L0 ≡ L2.

axiom thin_trans_ge: ∀d1,e1,L1,L. ↓[d1, e1] L1 ≡ L →
                     ∀e2,L2. ↓[0, e2] L ≡ L2 → d1 ≤ e2 → ↓[0, e1 + e2] L1 ≡ L2.
