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

include "lambda-delta/reduction/tpr_defs.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

inductive lpr: lenv → lenv → Prop ≝
| lpr_sort: lpr (⋆) (⋆)
| lpr_item: ∀K1,K2,I,V1,V2.
            lpr K1 K2 → V1 ⇒ V2 → lpr (K1. 𝕓{I} V1) (K2. 𝕓{I} V2) (*𝕓*)
.

interpretation
  "context-free parallel reduction (environment)"
  'PRed L1 L2 = (lpr L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpr_inv_item1_aux: ∀L1,L2. L1 ⇒ L2 → ∀K1,I,V1. L1 = K1. 𝕓{I} V1 →
                         ∃∃K2,V2. K1 ⇒ K2 & V1 ⇒ V2 & L2 = K2. 𝕓{I} V2.
#L1 #L2 #H elim H -H L1 L2
[ #K1 #I #V1 #H destruct
| #K1 #K2 #I #V1 #V2 #HK12 #HV12 #_ #L #J #W #H destruct - K1 I V1 /2 width=5/
]
qed.

lemma lpr_inv_item1: ∀K1,I,V1,L2. K1. 𝕓{I} V1 ⇒ L2 →
                     ∃∃K2,V2. K1 ⇒ K2 & V1 ⇒ V2 & L2 = K2. 𝕓{I} V2.
/2/ qed.
