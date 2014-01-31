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

include "basic_2/relocation/ldrop_append.ma".
include "basic_2/reduction/crr.ma".

(* REDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION **************************)

(* Advanved properties ******************************************************)

lemma crr_append_sn: ∀G,L,K,T. ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄  → ⦃G, K @@ L⦄ ⊢ ➡ 𝐑⦃T⦄.
#G #L #K0 #T #H elim H -L -T /2 width=1/
#L #K #V #i #HLK
lapply (ldrop_fwd_length_lt2 … HLK) #Hi
lapply (ldrop_O1_append_sn_le … HLK … K0) -HLK /2 width=2/ -Hi /2 width=3/
qed.

lemma trr_crr: ∀G,L,T. ⦃G, ⋆⦄ ⊢ ➡ 𝐑⦃T⦄ → ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄.
#G #L #T #H lapply (crr_append_sn … H) //
qed.

(* Advanced inversion lemmas ************************************************)

fact crr_inv_labst_last_aux: ∀G,L1,T,W. ⦃G, L1⦄ ⊢ ➡ 𝐑⦃T⦄  →
                             ∀L2. L1 = ⋆.ⓛW @@ L2 → ⦃G, L2⦄ ⊢ ➡ 𝐑⦃T⦄.
#G #L1 #T #W #H elim H -L1 -T /2 width=1/ /3 width=1/
[ #L1 #K1 #V1 #i #HLK1 #L2 #H destruct
  lapply (ldrop_fwd_length_lt2 … HLK1)
  >append_length >commutative_plus normalize in ⊢ (??% → ?); #H
  elim (le_to_or_lt_eq i (|L2|)) /2 width=1/ -H #Hi destruct
  [ elim (ldrop_O1_lt … Hi) #I2 #K2 #V2 #HLK2
    lapply (ldrop_O1_inv_append1_le … HLK1 … HLK2) -HLK1 /2 width=2/ -Hi
    normalize #H destruct /2 width=3/
  | lapply (ldrop_O1_inv_append1_ge … HLK1 ?) -HLK1 // <minus_n_n #H
    lapply (ldrop_inv_O2 … H) -H #H destruct
  ]
| #a #I #L1 #V #T #HI #_ #IHT #L2 #H destruct /3 width=1/
]
qed.

lemma crr_inv_labst_last: ∀G,L,T,W. ⦃G, ⋆.ⓛW @@ L⦄ ⊢ ➡ 𝐑⦃T⦄  → ⦃G, L⦄ ⊢ ➡ 𝐑⦃T⦄.
/2 width=4/ qed-.

lemma crr_inv_trr: ∀G,T,W. ⦃G, ⋆.ⓛW⦄ ⊢ ➡ 𝐑⦃T⦄  → ⦃G, ⋆⦄ ⊢ ➡ 𝐑⦃T⦄.
/2 width=4/ qed-.
