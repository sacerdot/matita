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

include "basic_2/unfold/ltpss.ma".

(* ITERATED PARTIAL UNFOLD ON LOCAL ENVIRONMENTS ****************************)

definition ltpsss: nat → nat → relation lenv ≝
                   λd,e. TC … (ltpss d e).

interpretation "repeated partial unfold (local environment)"
   'PSubstStars L1 d e L2 = (ltpsss d e L1 L2).

(* Basic eliminators ********************************************************)

lemma ltpsss_ind: ∀d,e,L1. ∀R:predicate lenv. R L1 →
                  (∀L,L2. L1 [d, e] ▶** L → L [d, e] ▶* L2 → R L → R L2) →
                  ∀L2. L1 [d, e] ▶** L2 → R L2.
#d #e #L1 #R #HL1 #IHL1 #L2 #HL12 @(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma ltpsss_ind_dx: ∀d,e,L2. ∀R:predicate lenv. R L2 →
                     (∀L1,L. L1 [d, e] ▶* L → L [d, e] ▶** L2 → R L → R L1) →
                     ∀L1. L1 [d, e] ▶** L2 → R L1.
#d #e #L2 #R #HL2 #IHL2 #L1 #HL12 @(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma ltpsss_strap1: ∀L1,L,L2,d,e.
                     L1 [d, e] ▶** L → L [d, e] ▶* L2 → L1 [d, e] ▶** L2. 
/2 width=3/ qed.

lemma ltpsss_strap2: ∀L1,L,L2,d,e.
                     L1 [d, e] ▶* L → L [d, e] ▶** L2 → L1 [d, e] ▶** L2. 
/2 width=3/ qed.

lemma ltpsss_refl: ∀L,d,e. L [d, e] ▶** L.
/2 width=1/ qed.

lemma ltpsss_weak_all: ∀L1,L2,d,e. L1 [d, e] ▶** L2 → L1 [0, |L2|] ▶** L2.
#L1 #L2 #d #e #H @(ltpsss_ind … H) -L2 //
#L #L2 #_ #HL2
>(ltpss_fwd_length … HL2) /3 width=5/
qed.

(* Basic forward lemmas *****************************************************)

lemma ltpsss_fwd_length: ∀L1,L2,d,e. L1 [d, e] ▶** L2 → |L1| = |L2|.
#L1 #L2 #d #e #H @(ltpsss_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL12 >IHL12 -IHL12
/2 width=3 by ltpss_fwd_length/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma ltpsss_inv_refl_O2: ∀d,L1,L2. L1 [d, 0] ▶** L2 → L1 = L2.
#d #L1 #L2 #H @(ltpsss_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL <(ltpss_inv_refl_O2 … HL2) -HL2 //
qed-.

lemma ltpsss_inv_atom1: ∀d,e,L2. ⋆ [d, e] ▶** L2 → L2 = ⋆.
#d #e #L2 #H @(ltpsss_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL destruct
>(ltpss_inv_atom1 … HL2) -HL2 //
qed-.

lemma ltpsss_inv_atom2: ∀d,e,L1. L1 [d, e] ▶** ⋆ → L1 = ⋆.
#d #e #L1 #H @(ltpsss_ind_dx … H) -L1 //
#L1 #L #HL1 #_ #IHL2 destruct
>(ltpss_inv_atom2 … HL1) -HL1 //
qed.
