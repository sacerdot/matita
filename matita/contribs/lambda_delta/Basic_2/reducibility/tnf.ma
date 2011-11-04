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

include "Basic_2/substitution/tps_lift.ma".
include "Basic_2/reducibility/trf.ma".
include "Basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE NORMAL TERMS ************************************************)

definition tnf: term → Prop ≝
   NF … tpr (eq …).

interpretation
   "context-free normality (term)"
   'Normal T = (tnf T).

(* Basic inversion lemmas ***************************************************)

lemma tnf_inv_abst: ∀V,T. ℕ[𝕔{Abst}V.T] → ℕ[V] ∧ ℕ[T].
#V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (𝕔{Abst}V2.T1) ?) -HVT1 /2/ -HV2 #H destruct -V1 T1 //
| #T2 #HT2 lapply (HVT1 (𝕔{Abst}V1.T2) ?) -HVT1 /2/ -HT2 #H destruct -V1 T1 //
]
qed.

lemma tnf_inv_appl: ∀V,T. ℕ[𝕔{Appl}V.T] → ∧∧ ℕ[V] & ℕ[T] & 𝕊[T].
#V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (𝕔{Appl}V2.T1) ?) -HVT1 /2/ -HV2 #H destruct -V1 T1 //
| #T2 #HT2 lapply (HVT1 (𝕔{Appl}V1.T2) ?) -HVT1 /2/ -HT2 #H destruct -V1 T1 //
| generalize in match HVT1 -HVT1; elim T1 -T1 * // * #W1 #U1 #_ #_ #H
  [ elim (lift_total V1 0 1) #V2 #HV12
    lapply (H (𝕔{Abbr}W1.𝕔{Appl}V2.U1) ?) -H /2/ -HV12 #H destruct
  | lapply (H (𝕔{Abbr}V1.U1) ?) -H /2/ #H destruct
]
qed.

axiom tnf_inv_abbr: ∀V,T. ℕ[𝕔{Abbr}V.T] → False.

lemma tnf_inv_cast: ∀V,T. ℕ[𝕔{Cast}V.T] → False.
#V #T #H lapply (H T ?) -H /2/
qed.

(* Basic properties *********************************************************)

lemma tpr_tif_eq: ∀T1,T2. T1 ⇒ T2 →  𝕀[T1] → T1 = T2.
#T1 #T2 #H elim H -T1 T2
[ //
| * #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (tif_inv_appl … H) -H #HV1 #HT1 #_
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  | elim (tif_inv_cast … H)
  ]
| #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #H
  elim (tif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| * #V1 #V2 #T1 #T #T2 #_ #_ #HT2 #IHV1 #IHT1 #H
  [ -HT2 IHV1 IHT1; elim (tif_inv_abbr … H)
  | <(tps_inv_refl_SO2 … HT2 ?) -HT2 //
    elim (tif_inv_abst … H) -H #HV1 #HT1
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  ]
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (tif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #V1 #T1 #T2 #T #_ #_ #_ #H
  elim (tif_inv_abbr … H)
| #V1 #T1 #T #_ #_ #H
  elim (tif_inv_cast … H)
]
qed.

theorem tif_tnf: ∀T1.  𝕀[T1] → ℕ[T1].
/2/ qed.

(* Note: this property is unusual *)
theorem tnf_trf_false: ∀T1. ℝ[T1] → ℕ[T1] → False.
#T1 #H elim H -T1
[ #V #T #_ #IHV #H elim (tnf_inv_abst … H) -H /2/
| #V #T #_ #IHT #H elim (tnf_inv_abst … H) -H /2/
| #V #T #_ #IHV #H elim (tnf_inv_appl … H) -H /2/
| #V #T #_ #IHV #H elim (tnf_inv_appl … H) -H /2/
| #V #T #H elim (tnf_inv_abbr … H)
| #V #T #H elim (tnf_inv_cast … H)
| #V #W #T #H elim (tnf_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
]
qed.

theorem tnf_tif: ∀T1. ℕ[T1] → 𝕀[T1].
/2/ qed.

lemma tnf_abst: ∀V,T. ℕ[V] → ℕ[T] → ℕ[𝕔{Abst}V.T].
/4 width=1/ qed.

lemma tnf_appl: ∀V,T. ℕ[V] → ℕ[T] → 𝕊[T] → ℕ[𝕔{Appl}V.T].
/4 width=1/ qed.
