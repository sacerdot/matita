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

include "Basic_2/substitution/ltps.ma".
include "Basic_2/unfold/tpss.ma".

(* PARTIAL UNFOLD ON LOCAL ENVIRONMENTS *************************************)

definition ltpss: nat → nat → relation lenv ≝
                  λd,e. TC … (ltps d e).

interpretation "partial unfold (local environment)"
   'PSubstStar L1 d e L2 = (ltpss d e L1 L2).

(* Basic eliminators ********************************************************)

lemma ltpss_ind: ∀d,e,L1. ∀R:predicate lenv. R L1 →
                 (∀L,L2. L1 [d, e] ≫* L → L [d, e] ≫ L2 → R L → R L2) →
                 ∀L2. L1 [d, e] ≫* L2 → R L2.
#d #e #L1 #R #HL1 #IHL1 #L2 #HL12 @(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma ltpss_strap: ∀L1,L,L2,d,e.
                   L1 [d, e] ≫ L → L [d, e] ≫* L2 → L1 [d, e] ≫* L2. 
/2/ qed.

lemma ltpss_refl: ∀L,d,e. L [d, e] ≫* L.
/2/ qed.

(* Basic inversion lemmas ***************************************************)

lemma ltpss_inv_refl_O2: ∀d,L1,L2. L1 [d, 0] ≫* L2 → L1 = L2.
#d #L1 #L2 #H @(ltpss_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL <(ltps_inv_refl_O2 … HL2) -HL2 //
qed-.

lemma ltpss_inv_atom1: ∀d,e,L2. ⋆ [d, e] ≫* L2 → L2 = ⋆.
#d #e #L2 #H @(ltpss_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL destruct -L
>(ltps_inv_atom1 … HL2) -HL2 //
qed-.

fact ltpss_inv_atom2_aux: ∀d,e,L1,L2.
                          L1 [d, e] ≫* L2 → L2 = ⋆ → L1 = ⋆.
#d #e #L1 #L2 #H @(ltpss_ind … H) -L2 //
#L2 #L #_ #HL2 #IHL2 #H destruct -L;
lapply (ltps_inv_atom2 … HL2) -HL2 /2/
qed.

lemma ltpss_inv_atom2: ∀d,e,L1. L1 [d, e] ≫* ⋆ → L1 = ⋆.
/2 width=5/ qed-.
(*
fact ltps_inv_tps22_aux: ∀d,e,L1,L2. L1 [d, e] ≫ L2 → d = 0 → 0 < e →
                         ∀K2,I,V2. L2 = K2. 𝕓{I} V2 →
                         ∃∃K1,V1. K1 [0, e - 1] ≫ K2 &
                                  K2 ⊢ V1 [0, e - 1] ≫ V2 &
                                  L1 = K1. 𝕓{I} V1.
#d #e #L1 #L2 * -d e L1 L2
[ #d #e #_ #_ #K1 #I #V1 #H destruct
| #L1 #I #V #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #_ #_ #K2 #J #W2 #H destruct -L2 I V2 /2 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H elim (plus_S_eq_O_false … H)
]
qed.

lemma ltps_inv_tps22: ∀e,L1,K2,I,V2. L1 [0, e] ≫ K2. 𝕓{I} V2 → 0 < e →
                      ∃∃K1,V1. K1 [0, e - 1] ≫ K2 & K2 ⊢ V1 [0, e - 1] ≫ V2 &
                               L1 = K1. 𝕓{I} V1.
/2 width=5/ qed.

fact ltps_inv_tps12_aux: ∀d,e,L1,L2. L1 [d, e] ≫ L2 → 0 < d →
                         ∀I,K2,V2. L2 = K2. 𝕓{I} V2 →
                         ∃∃K1,V1. K1 [d - 1, e] ≫ K2 &
                                  K2 ⊢ V1 [d - 1, e] ≫ V2 &
                                  L1 = K1. 𝕓{I} V1.
#d #e #L1 #L2 * -d e L1 L2
[ #d #e #_ #I #K2 #V2 #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #_ #J #K2 #W2 #H destruct -L2 I V2
  /2 width=5/
]
qed.

lemma ltps_inv_tps12: ∀L1,K2,I,V2,d,e. L1 [d, e] ≫ K2. 𝕓{I} V2 → 0 < d →
                      ∃∃K1,V1. K1 [d - 1, e] ≫ K2 &
                                  K2 ⊢ V1 [d - 1, e] ≫ V2 &
                                  L1 = K1. 𝕓{I} V1.
/2/ qed.
*)
