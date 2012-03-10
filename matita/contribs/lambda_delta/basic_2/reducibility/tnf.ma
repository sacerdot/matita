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

include "Basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE NORMAL TERMS ************************************************)

definition tnf: predicate term ≝ NF … tpr (eq …).

interpretation
   "context-free normality (term)"
   'Normal T = (tnf T).

(* Basic inversion lemmas ***************************************************)

lemma tnf_inv_abst: ∀V,T. 𝐍[ⓛV.T] → 𝐍[V] ∧ 𝐍[T].
#V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛV2.T1) ?) -HVT1 /2 width=1/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓛV1.T2) ?) -HVT1 /2 width=1/ -HT2 #H destruct //
]
qed-.

lemma tnf_inv_appl: ∀V,T. 𝐍[ⓐV.T] → ∧∧ 𝐍[V] & 𝐍[T] & 𝐒[T].
#V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1/ -HT2 #H destruct //
| generalize in match HVT1; -HVT1 elim T1 -T1 * // * #W1 #U1 #_ #_ #H
  [ elim (lift_total V1 0 1) #V2 #HV12
    lapply (H (ⓓW1.ⓐV2.U1) ?) -H /2 width=3/ -HV12 #H destruct
  | lapply (H (ⓓV1.U1) ?) -H /2 width=1/ #H destruct
]
qed-.

lemma tnf_inv_abbr: ∀V,T. 𝐍[ⓓV.T] → False.
#V #T #H elim (is_lift_dec T 0 1)
[ * #U #HTU
  lapply (H U ?) -H /2 width=3/ #H destruct
  elim (lift_inv_pair_xy_y … HTU)
| #HT
  elim (tps_full (⋆) V T (⋆. ⓓV) 0 ?) // #T2 #T1 #HT2 #HT12
  lapply (H (ⓓV.T2) ?) -H /2 width=3/ -HT2 #H destruct /3 width=2/
]
qed.

lemma tnf_inv_cast: ∀V,T. 𝐍[ⓣV.T] → False.
#V #T #H lapply (H T ?) -H /2 width=1/ #H
@(discr_tpair_xy_y … H)
qed-.
