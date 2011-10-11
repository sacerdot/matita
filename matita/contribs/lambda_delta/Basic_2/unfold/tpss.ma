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

include "Basic_2/substitution/tps.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

definition tpss: nat → nat → lenv → relation term ≝
                 λd,e,L. TC … (tps d e L).

interpretation "partial unfold (term)"
   'PSubstStar L T1 d e T2 = (tpss d e L T1 T2).

(* Basic eliminators ********************************************************)

lemma tpss_ind: ∀d,e,L,T1. ∀R: term → Prop. R T1 →
                (∀T,T2. L ⊢ T1 [d, e] ≫* T → L ⊢ T [d, e] ≫ T2 → R T → R T2) →
                ∀T2. L ⊢ T1 [d, e] ≫* T2 → R T2.
#d #e #L #T1 #R #HT1 #IHT1 #T2 #HT12 @(TC_star_ind … HT1 IHT1 … HT12) //
qed.

(* Basic properties *********************************************************)

lemma tpss_strap: ∀L,T1,T,T2,d,e. 
                  L ⊢ T1 [d, e] ≫ T → L ⊢ T [d, e] ≫* T2 → L ⊢ T1 [d, e] ≫* T2. 
/2/ qed.

lemma tpss_lsubs_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ≫* T2 →
                       ∀L2. L1 [d, e] ≼ L2 → L2 ⊢ T1 [d, e] ≫* T2.
/3/ qed.

lemma tpss_refl: ∀d,e,L,T. L ⊢ T [d, e] ≫* T.
/2/ qed.

lemma tpss_bind: ∀L,V1,V2,d,e. L ⊢ V1 [d, e] ≫* V2 →
                 ∀I,T1,T2. L. 𝕓{I} V2 ⊢ T1 [d + 1, e] ≫* T2 →
                 L ⊢ 𝕓{I} V1. T1 [d, e] ≫* 𝕓{I} V2. T2.
#L #V1 #V2 #d #e #HV12 elim HV12 -HV12 V2
[ #V2 #HV12 #I #T1 #T2 #HT12 elim HT12 -HT12 T2
  [ /3 width=5/
  | #T #T2 #_ #HT2 #IHT @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
  ]
| #V #V2 #_ #HV12 #IHV #I #T1 #T2 #HT12
  lapply (tpss_lsubs_conf … HT12 (L. 𝕓{I} V) ?) -HT12 /2/ #HT12
  lapply (IHV … HT12) -IHV HT12 #HT12 @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma tpss_flat: ∀L,I,V1,V2,T1,T2,d,e.
                 L ⊢ V1 [d, e] ≫ * V2 → L ⊢ T1 [d, e] ≫* T2 →
                 L ⊢ 𝕗{I} V1. T1 [d, e] ≫* 𝕗{I} V2. T2.
#L #I #V1 #V2 #T1 #T2 #d #e #HV12 elim HV12 -HV12 V2
[ #V2 #HV12 #HT12 elim HT12 -HT12 T2
  [ /3/
  | #T #T2 #_ #HT2 #IHT @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
  ]
| #V #V2 #_ #HV12 #IHV #HT12
  lapply (IHV … HT12) -IHV HT12 #HT12 @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma tpss_weak: ∀L,T1,T2,d1,e1. L ⊢ T1 [d1, e1] ≫* T2 →
                 ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                 L ⊢ T1 [d2, e2] ≫* T2.
#L #T1 #T2 #d1 #e1 #H #d1 #d2 #Hd21 #Hde12 @(tpss_ind … H) -H T2
[ //
| #T #T2 #_ #HT12 #IHT
  lapply (tps_weak … HT12 … Hd21 Hde12) -HT12 Hd21 Hde12 /2/
]
qed.

lemma tpss_weak_top: ∀L,T1,T2,d,e.
                     L ⊢ T1 [d, e] ≫* T2 → L ⊢ T1 [d, |L| - d] ≫* T2.
#L #T1 #T2 #d #e #H @(tpss_ind … H) -H T2
[ //
| #T #T2 #_ #HT12 #IHT
  lapply (tps_weak_top … HT12) -HT12 /2/
]
qed.

lemma tpss_weak_all: ∀L,T1,T2,d,e.
                     L ⊢ T1 [d, e] ≫* T2 → L ⊢ T1 [0, |L|] ≫* T2.
#L #T1 #T2 #d #e #HT12
lapply (tpss_weak … HT12 0 (d + e) ? ?) -HT12 // #HT12
lapply (tpss_weak_top … HT12) //
qed.

(* Basic inversion lemmas ***************************************************)

(* Note: this can be derived from tpss_inv_atom1 *)
lemma tpss_inv_sort1: ∀L,T2,k,d,e. L ⊢ ⋆k [d, e] ≫* T2 → T2 = ⋆k.
#L #T2 #k #d #e #H @(tpss_ind … H) -H T2
[ //
| #T #T2 #_ #HT2 #IHT destruct -T
  >(tps_inv_sort1 … HT2) -HT2 //
]
qed.

lemma tpss_inv_bind1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕓{I} V1. T1 [d, e] ≫* U2 →
                      ∃∃V2,T2. L ⊢ V1 [d, e] ≫* V2 & 
                               L. 𝕓{I} V2 ⊢ T1 [d + 1, e] ≫* T2 &
                               U2 =  𝕓{I} V2. T2.
#d #e #L #I #V1 #T1 #U2 #H @(tpss_ind … H) -H U2
[ /2 width=5/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct -U;
  elim (tps_inv_bind1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H
  lapply (tpss_lsubs_conf … HT1 (L. 𝕓{I} V2) ?) -HT1 /3 width=5/
]
qed.

lemma tpss_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ 𝕗{I} V1. T1 [d, e] ≫* U2 →
                      ∃∃V2,T2. L ⊢ V1 [d, e] ≫* V2 & L ⊢ T1 [d, e] ≫* T2 &
                               U2 =  𝕗{I} V2. T2.
#d #e #L #I #V1 #T1 #U2 #H @(tpss_ind … H) -H U2
[ /2 width=5/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct -U;
  elim (tps_inv_flat1 … HU2) -HU2 /3 width=5/
]
qed.

lemma tpss_inv_refl_O2: ∀L,T1,T2,d. L ⊢ T1 [d, 0] ≫* T2 → T1 = T2.
#L #T1 #T2 #d #H @(tpss_ind … H) -H T2
[ //
| #T #T2 #_ #HT2 #IHT <(tps_inv_refl_O2 … HT2) -HT2 //
]
qed.
