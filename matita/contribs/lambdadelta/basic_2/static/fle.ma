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
include "basic_2/syntax/lveq.ma".
include "basic_2/static/frees.ma".

(* FREE VARIABLES INCLUSION FOR RESTRICTED CLOSURES *************************)

definition fle: bi_relation lenv term ≝ λL1,T1,L2,T2.
                ∃∃n1,n2,f1,f2. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 &
                               L1 ≋ⓧ*[n1, n2] L2 & ⫱*[n1]f1 ⊆ ⫱*[n2]f2.

interpretation "free variables inclusion (restricted closure)"
   'SubSetEq L1 T1 L2 T2 = (fle L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fle_sort: ∀L,s1,s2. ⦃L, ⋆s1⦄ ⊆ ⦃L, ⋆s2⦄.
#L elim (lveq_refl L)
/3 width=8 by frees_sort, sle_refl, ex4_4_intro/
qed.

lemma fle_gref: ∀L,l1,l2. ⦃L, §l1⦄ ⊆ ⦃L, §l2⦄.
#L elim (lveq_refl L)
/3 width=8 by frees_gref, sle_refl, ex4_4_intro/
qed.

(* Basic inversion lemmas ***************************************************)
(*
fact fle_inv_voids_aux: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                        ∀K1,K2,n1,n2. |K1| = |K2| → L1 = ⓧ*[n1]K1 → L2 = ⓧ*[n2]K2 →
                        ∃∃f1,f2. ⓧ*[n1]K1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & ⓧ*[n2]K2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & ⫱*[n1]f1 ⊆ ⫱*[n2]f2.
#L1 #L2 #T1 #T2 * -L1 -L2
#f1 #f2 #L1 #L2 #n1 #n2 #Hf1 #Hf2 #HL12 #Hf12 #Y1 #Y2 #x1 #x2 #HY12 #H1 #H2 destruct
>H1 in Hf1; >H2 in Hf2; #Hf2 #Hf1
@(ex3_2_intro … Hf1 Hf2) -Hf1 -Hf2

elim (voids_inj_length … H1) // -H -HL12 -HY #H1 #H2 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma fle_inv_voids_sn: ∀L1,L2,T1,T2,n. ⦃ⓧ*[n]L1, T1⦄ ⊆ ⦃L2, T2⦄ → |L1| = |L2| →
                        ∃∃f1,f2. ⓧ*[n]L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 & L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & ⫱*[n]f1 ⊆ f2.
/2 width=3 by fle_inv_voids_sn_aux/ qed-.
*)