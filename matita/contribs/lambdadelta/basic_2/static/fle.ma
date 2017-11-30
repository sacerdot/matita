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

include "ground_2/relocation/rtmap_id.ma".
include "basic_2/notation/relations/subseteq_4.ma".
include "basic_2/syntax/voids_length.ma".
include "basic_2/static/frees.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

inductive fle (T2) (L2) (T1): predicate lenv ≝
| fle_intro: ∀f1,f2,L1,n. ⓧ*[n]L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 → L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 →
             |L1| = |L2| → ⫱*[n]f1 ⊆ f2 → fle T2 L2 T1 (ⓧ*[n]L1)
.

interpretation "free variables inclusion (restricted closure)"
   'SubSetEq L1 T1 L2 T2 = (fle T2 L2 T1 L1).

(* Basic properties *********************************************************)

lemma fle_sort: ∀L1,L2. |L1| = |L2| → ∀s1,s2. ⦃L1, ⋆s1⦄ ⊆ ⦃L2, ⋆s2⦄.
/3 width=5 by frees_sort, sle_refl, fle_intro/ qed.

lemma fle_gref: ∀L1,L2. |L1| = |L2| → ∀l1,l2. ⦃L1, §l1⦄ ⊆ ⦃L2, §l2⦄.
/3 width=5 by frees_gref, sle_refl, fle_intro/ qed.

(* Basic inversion lemmas ***************************************************)

fact fle_inv_voids_sn_aux: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                           ∀K1,n. |K1| = |L2| → L1 = ⓧ*[n]K1 →
                           ∃∃f1,f2. ⓧ*[n]K1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & ⫱*[n]f1 ⊆ f2.
#L1 #L2 #T1 #T2 * -L1 #f1 #f2 #L1 #n #Hf1 #Hf2 #HL12 #Hf12 #Y #x #HY #H destruct
elim (voids_inj_length … H) // -H -HL12 -HY #H1 #H2 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma fle_inv_voids_sn: ∀L1,L2,T1,T2,n. ⦃ⓧ*[n]L1, T1⦄ ⊆ ⦃L2, T2⦄ → |L1| = |L2| →
                        ∃∃f1,f2. ⓧ*[n]L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & ⫱*[n]f1 ⊆ f2.
/2 width=3 by fle_inv_voids_sn_aux/ qed-.
