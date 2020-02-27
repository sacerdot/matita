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

notation "hvbox( L ⊢ break term 46 T1 break ▶ * [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $L $T1 $d $e $T2 }.

include "basic_2/substitution/tps.ma".

(* PARTIAL UNFOLD ON TERMS **************************************************)

definition tpss: nat → nat → lenv → relation term ≝
                 λd,e,L. TC … (tps d e L).

interpretation "partial unfold (term)"
   'PSubstStar L T1 d e T2 = (tpss d e L T1 T2).

(* Basic eliminators ********************************************************)

lemma tpss_ind: ∀d,e,L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. L ⊢ T1 ▶* [d, e] T → L ⊢ T ▶ [d, e] T2 → R T → R T2) →
                ∀T2. L ⊢ T1 ▶* [d, e] T2 → R T2.
#d #e #L #T1 #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma tpss_ind_dx: ∀d,e,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. L ⊢ T1 ▶ [d, e] T → L ⊢ T ▶* [d, e] T2 → R T → R T1) →
                   ∀T1. L ⊢ T1 ▶* [d, e] T2 → R T1.
#d #e #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma tps_tpss: ∀L,T1,T2,d,e. L ⊢ T1 ▶ [d, e] T2 → L ⊢ T1 ▶* [d, e] T2.
/2 width=1/ qed.

lemma tpss_strap1: ∀L,T1,T,T2,d,e.
                   L ⊢ T1 ▶* [d, e] T → L ⊢ T ▶ [d, e] T2 → L ⊢ T1 ▶* [d, e] T2.
/2 width=3/ qed.

lemma tpss_strap2: ∀L,T1,T,T2,d,e.
                   L ⊢ T1 ▶ [d, e] T → L ⊢ T ▶* [d, e] T2 → L ⊢ T1 ▶* [d, e] T2.
/2 width=3/ qed.

lemma tpss_lsubr_trans: ∀L1,T1,T2,d,e. L1 ⊢ T1 ▶* [d, e] T2 →
                        ∀L2. L2 ⊑ [d, e] L1 → L2 ⊢ T1 ▶* [d, e] T2.
/3 width=3/ qed.

lemma tpss_refl: ∀d,e,L,T. L ⊢ T ▶* [d, e] T.
/2 width=1/ qed.

lemma tpss_bind: ∀L,V1,V2,d,e. L ⊢ V1 ▶* [d, e] V2 →
                 ∀a,I,T1,T2. L. ⓑ{I} V2 ⊢ T1 ▶* [d + 1, e] T2 →
                 L ⊢ ⓑ{a,I} V1. T1 ▶* [d, e] ⓑ{a,I} V2. T2.
#L #V1 #V2 #d #e #HV12 elim HV12 -V2
[ #V2 #HV12 #a #I #T1 #T2 #HT12 elim HT12 -T2
  [ /3 width=5/
  | #T #T2 #_ #HT2 #IHT @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
  ]
| #V #V2 #_ #HV12 #IHV #a #I #T1 #T2 #HT12
  lapply (tpss_lsubr_trans … HT12 (L. ⓑ{I} V) ?) -HT12 /2 width=1/ #HT12
  lapply (IHV a … HT12) -IHV -HT12 #HT12 @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma tpss_flat: ∀L,I,V1,V2,T1,T2,d,e.
                 L ⊢ V1 ▶* [d, e] V2 → L ⊢ T1 ▶* [d, e] T2 →
                 L ⊢ ⓕ{I} V1. T1 ▶* [d, e] ⓕ{I} V2. T2.
#L #I #V1 #V2 #T1 #T2 #d #e #HV12 elim HV12 -V2
[ #V2 #HV12 #HT12 elim HT12 -T2
  [ /3 width=1/
  | #T #T2 #_ #HT2 #IHT @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
  ]
| #V #V2 #_ #HV12 #IHV #HT12
  lapply (IHV … HT12) -IHV -HT12 #HT12 @step /2 width=5/ (**) (* /3 width=5/ is too slow *)
]
qed.

lemma tpss_weak: ∀L,T1,T2,d1,e1. L ⊢ T1 ▶* [d1, e1] T2 →
                 ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                 L ⊢ T1 ▶* [d2, e2] T2.
#L #T1 #T2 #d1 #e1 #H #d1 #d2 #Hd21 #Hde12 @(tpss_ind … H) -T2
[ //
| #T #T2 #_ #HT12 #IHT
  lapply (tps_weak … HT12 … Hd21 Hde12) -HT12 -Hd21 -Hde12 /2 width=3/
]
qed.

lemma tpss_weak_top: ∀L,T1,T2,d,e.
                     L ⊢ T1 ▶* [d, e] T2 → L ⊢ T1 ▶* [d, |L| - d] T2.
#L #T1 #T2 #d #e #H @(tpss_ind … H) -T2
[ //
| #T #T2 #_ #HT12 #IHT
  lapply (tps_weak_top … HT12) -HT12 /2 width=3/
]
qed.

lemma tpss_weak_full: ∀L,T1,T2,d,e.
                      L ⊢ T1 ▶* [d, e] T2 → L ⊢ T1 ▶* [0, |L|] T2.
#L #T1 #T2 #d #e #HT12
lapply (tpss_weak … HT12 0 (d + e) ? ?) -HT12 // #HT12
lapply (tpss_weak_top … HT12) //
qed.

lemma tpss_append: ∀K,T1,T2,d,e. K ⊢ T1 ▶* [d, e] T2 →
                   ∀L. L @@ K ⊢ T1 ▶* [d, e] T2.
#K #T1 #T2 #d #e #H @(tpss_ind … H) -T2 // /3 width=3/
qed.

(* Basic inversion lemmas ***************************************************)

(* Note: this can be derived from tpss_inv_atom1 *)
lemma tpss_inv_sort1: ∀L,T2,k,d,e. L ⊢ ⋆k ▶* [d, e] T2 → T2 = ⋆k.
#L #T2 #k #d #e #H @(tpss_ind … H) -T2
[ //
| #T #T2 #_ #HT2 #IHT destruct
  >(tps_inv_sort1 … HT2) -HT2 //
]
qed-.

(* Note: this can be derived from tpss_inv_atom1 *)
lemma tpss_inv_gref1: ∀L,T2,p,d,e. L ⊢ §p ▶* [d, e] T2 → T2 = §p.
#L #T2 #p #d #e #H @(tpss_ind … H) -T2
[ //
| #T #T2 #_ #HT2 #IHT destruct
  >(tps_inv_gref1 … HT2) -HT2 //
]
qed-.

lemma tpss_inv_bind1: ∀d,e,L,a,I,V1,T1,U2. L ⊢ ⓑ{a,I} V1. T1 ▶* [d, e] U2 →
                      ∃∃V2,T2. L ⊢ V1 ▶* [d, e] V2 &
                               L. ⓑ{I} V2 ⊢ T1 ▶* [d + 1, e] T2 &
                               U2 = ⓑ{a,I} V2. T2.
#d #e #L #a #I #V1 #T1 #U2 #H @(tpss_ind … H) -U2
[ /2 width=5/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (tps_inv_bind1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H
  lapply (tpss_lsubr_trans … HT1 (L. ⓑ{I} V2) ?) -HT1 /2 width=1/ /3 width=5/
]
qed-.

lemma tpss_inv_flat1: ∀d,e,L,I,V1,T1,U2. L ⊢ ⓕ{I} V1. T1 ▶* [d, e] U2 →
                      ∃∃V2,T2. L ⊢ V1 ▶* [d, e] V2 & L ⊢ T1 ▶* [d, e] T2 &
                               U2 =  ⓕ{I} V2. T2.
#d #e #L #I #V1 #T1 #U2 #H @(tpss_ind … H) -U2
[ /2 width=5/
| #U #U2 #_ #HU2 * #V #T #HV1 #HT1 #H destruct
  elim (tps_inv_flat1 … HU2) -HU2 /3 width=5/
]
qed-.

lemma tpss_inv_refl_O2: ∀L,T1,T2,d. L ⊢ T1 ▶* [d, 0] T2 → T1 = T2.
#L #T1 #T2 #d #H @(tpss_ind … H) -T2
[ //
| #T #T2 #_ #HT2 #IHT <(tps_inv_refl_O2 … HT2) -HT2 //
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma tpss_fwd_tw: ∀L,T1,T2,d,e. L ⊢ T1 ▶* [d, e] T2 → ♯{T1} ≤ ♯{T2}.
#L #T1 #T2 #d #e #H @(tpss_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1
lapply (tps_fwd_tw … HT2) -HT2 #HT2
@(transitive_le … IHT1) //
qed-.

lemma tpss_fwd_shift1: ∀L,L1,T1,T,d,e. L ⊢ L1 @@ T1 ▶*[d, e] T →
                       ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#L #L1 #T1 #T #d #e #H @(tpss_ind … H) -T
[ /2 width=4/
| #T #X #_ #H0 * #L0 #T0 #HL10 #H destruct
  elim (tps_fwd_shift1 … H0) -H0 #L2 #T2 #HL02 #H destruct /2 width=4/
]
qed-.
