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

include "basic_2/substitution/drop_append.ma".
include "basic_2/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties on append for local environments ******************************)

lemma frees_append: ∀L2,U,d,i. L2 ⊢ i ϵ 𝐅*[d]⦃U⦄ → i ≤ |L2| →
                    ∀L1. L1 @@ L2 ⊢ i ϵ 𝐅*[d]⦃U⦄.
#L2 #U #d #i #H elim H -L2 -U -d -i /3 width=2 by frees_eq/
#I #L2 #K2 #U #W #d #i #j #Hdj #Hji #HnU #HLK2 #_ #IHW #Hi #L1
lapply (drop_fwd_length_minus2 … HLK2) normalize #H0
lapply (drop_O1_append_sn_le … HLK2 … L1) -HLK2
[ -I -L1 -K2 -U -W -d /3 width=3 by lt_to_le, lt_to_le_to_lt/
| #HLK2 @(frees_be … HnU HLK2) // -HnU -HLK2 @IHW -IHW
  >(minus_plus_m_m (|K2|) 1) >H0 -H0 /2 width=1 by monotonic_le_minus_l2/
]
qed.

(* Inversion lemmas on append for local environments ************************)

fact frees_inv_append_aux: ∀L,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃U⦄ → ∀L1,L2. L = L1 @@ L2 →
                           i ≤ |L2| → L2 ⊢ i ϵ 𝐅*[d]⦃U⦄.
#L #U #d #i #H elim H -L -U -d -i /3 width=2 by frees_eq/
#Z #L #Y #U #X #d #i #j #Hdj #Hji #HnU #HLY #_ #IHW #L1 #L2 #H #Hi destruct
elim (drop_O1_lt (Ⓕ) L2 j) [2: -Z -Y -L1 -X -U -d /2 width=3 by lt_to_le_to_lt/ ]
#I #K2 #W #HLK2 lapply (drop_fwd_length_minus2 … HLK2) normalize #H0
lapply (drop_O1_inv_append1_le … HLY … HLK2) -HLY
[ -Z -I -Y -K2 -L1 -X -U -W -d /3 width=3 by lt_to_le, lt_to_le_to_lt/
| normalize #H destruct
  @(frees_be … HnU HLK2) -HnU -HLK2 // @IHW -IHW //
  >(minus_plus_m_m (|K2|) 1) >H0 -H0 /2 width=1 by monotonic_le_minus_l2/
]
qed-.

lemma frees_inv_append: ∀L1,L2,U,d,i. L1 @@ L2 ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                        i ≤ |L2| → L2 ⊢ i ϵ 𝐅*[d]⦃U⦄.
/2 width=4 by frees_inv_append_aux/ qed-.
