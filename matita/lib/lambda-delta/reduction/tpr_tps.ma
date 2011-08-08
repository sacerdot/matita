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

include "lambda-delta/reduction/lpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON TERMS *********************************)

axiom tpr_tps_lpr: ∀L1,L2. L1 ⇒ L2 → ∀T1,T2. T1 ⇒ T2 →
                   ∀d,e,U1. L1 ⊢ T1 [d, e] ≫ U1 →
                   ∃∃U2. U1 ⇒ U2 & L2 ⊢ T2 [d, e] ≫ U2.

lemma tpr_tps_bind: ∀I,V1,V2,T1,T2,U1. V1 ⇒ V2 → T1 ⇒ T2 →
                    ⋆. 𝕓{I} V1 ⊢ T1 [0, 1] ≫ U1 →
                    ∃∃U2. U1 ⇒ U2 & ⋆. 𝕓{I} V2 ⊢ T2 [0, 1] ≫ U2.
/3 width=5/ qed.
