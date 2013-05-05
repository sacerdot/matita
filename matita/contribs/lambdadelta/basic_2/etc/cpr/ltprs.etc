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

include "basic_2/reducibility/ltpr.ma".
include "basic_2/computation/tprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS ******************)

definition ltprs: relation lenv ≝ TC … ltpr.

interpretation
  "context-free parallel computation (environment)"
  'PRedStar L1 L2 = (ltprs L1 L2).

(* Basic eliminators ********************************************************)

lemma ltprs_ind: ∀L1. ∀R:predicate lenv. R L1 →
                 (∀L,L2. L1 ➡* L → L ➡ L2 → R L → R L2) →
                 ∀L2. L1 ➡* L2 → R L2.
#L1 #R #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma ltprs_ind_dx: ∀L2. ∀R:predicate lenv. R L2 →
                    (∀L1,L. L1 ➡ L → L ➡* L2 → R L → R L1) →
                    ∀L1. L1 ➡* L2 → R L1.
#L2 #R #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma ltprs_refl: reflexive … ltprs.
/2 width=1/ qed.

lemma ltpr_ltprs: ∀L1,L2. L1 ➡ L2 → L1 ➡* L2.
/2 width=1/ qed.

lemma ltprs_strap1: ∀L1,L,L2. L1 ➡* L → L ➡ L2 → L1 ➡* L2.
/2 width=3/ qed.

lemma ltprs_strap2: ∀L1,L,L2. L1 ➡ L → L ➡* L2 → L1 ➡* L2.
/2 width=3/ qed.

(* Basic inversion lemmas ***************************************************)

lemma ltprs_inv_atom1: ∀L2. ⋆ ➡* L2 → L2 = ⋆.
#L2 #H @(ltprs_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL1 destruct
>(ltpr_inv_atom1 … HL2) -L2 //
qed-.

lemma ltprs_inv_pair1: ∀I,K1,L2,V1. K1. ⓑ{I} V1 ➡* L2 →
                       ∃∃K2,V2. K1 ➡* K2 & V1 ➡* V2 & L2 = K2. ⓑ{I} V2.
#I #K1 #L2 #V1 #H @(ltprs_ind … H) -L2 /2 width=5/
#L #L2 #_ #HL2 * #K #V #HK1 #HV1 #H destruct
elim (ltpr_inv_pair1 … HL2) -HL2 #K2 #V2 #HK2 #HV2 #H destruct /3 width=5/
qed-.

lemma ltprs_inv_atom2: ∀L1. L1 ➡* ⋆ → L1 = ⋆.
#L1 #H @(ltprs_ind_dx … H) -L1 //
#L1 #L #HL1 #_ #IHL2 destruct
>(ltpr_inv_atom2 … HL1) -L1 //
qed-.

lemma ltprs_inv_pair2: ∀I,L1,K2,V2. L1 ➡* K2. ⓑ{I} V2 →
                       ∃∃K1,V1. K1 ➡* K2 & V1 ➡* V2 & L1 = K1. ⓑ{I} V1.
#I #L1 #K2 #V2 #H @(ltprs_ind_dx … H) -L1 /2 width=5/
#L1 #L #HL1 #_ * #K #V #HK2 #HV2 #H destruct
elim (ltpr_inv_pair2 … HL1) -HL1 #K1 #V1 #HK1 #HV1 #H destruct /3 width=5/
qed-.

(* Basic forward lemmas *****************************************************)

lemma ltprs_fwd_length: ∀L1,L2. L1 ➡* L2 → |L1| = |L2|.
#L1 #L2 #H @(ltprs_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL1
>IHL1 -L1 >(ltpr_fwd_length … HL2) -HL2 //
qed-.
