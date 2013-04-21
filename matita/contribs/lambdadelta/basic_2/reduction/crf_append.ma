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
include "basic_2/reduction/crf.ma".

(* CONTEXT-SENSITIVE REDUCIBLE TERMS ****************************************)

(* Advanved properties ******************************************************)

lemma crf_labst_last: ∀L,T,W. L ⊢ 𝐑⦃T⦄  → ⋆.ⓛW @@ L ⊢ 𝐑⦃T⦄.
#L #T #W #H elim H -L -T /2 width=1/
#L #K #V #i #HLK
lapply (ldrop_fwd_ldrop2_length … HLK) #Hi
lapply (ldrop_O1_append_sn_le … HLK … (⋆.ⓛW)) -HLK /2 width=2/ -Hi /2 width=3/
qed.

lemma crf_trf: ∀T,W. ⋆ ⊢ 𝐑⦃T⦄ → ⋆.ⓛW ⊢ 𝐑⦃T⦄.
#T #W #H lapply (crf_labst_last … W H) //
qed.

(* Advanced inversion lemmas ************************************************)

fact crf_inv_labst_last_aux: ∀L1,T,W. L1 ⊢ 𝐑⦃T⦄  →
                             ∀L2. L1 = ⋆.ⓛW @@ L2 → L2 ⊢ 𝐑⦃T⦄.
#L1 #T #W #H elim H -L1 -T /2 width=1/ /3 width=1/
[ #L1 #K1 #V1 #i #HLK1 #L2 #H destruct
  lapply (ldrop_fwd_ldrop2_length … HLK1)
  >append_length >commutative_plus normalize in ⊢ (??% → ?); #H
  elim (le_to_or_lt_eq i (|L2|) ?) /2 width=1/ -H #Hi destruct
  [ elim (ldrop_O1_lt … Hi) #I2 #K2 #V2 #HLK2
    lapply (ldrop_O1_inv_append1_le … HLK1 … HLK2) -HLK1 /2 width=2/ -Hi
    normalize #H destruct /2 width=3/
  | lapply (ldrop_O1_inv_append1_ge … HLK1 ?) -HLK1 // <minus_n_n #H
    lapply (ldrop_inv_refl … H) -H #H destruct
  ]
| #a #I #L1 #V #T #HI #_ #IHT #L2 #H destruct /3 width=1/
]
qed.

lemma crf_inv_labst_last: ∀L,T,W. ⋆.ⓛW @@ L ⊢ 𝐑⦃T⦄  → L ⊢ 𝐑⦃T⦄.
/2 width=4/ qed-.

lemma crf_inv_trf: ∀T,W. ⋆.ⓛW ⊢ 𝐑⦃T⦄  → ⋆ ⊢ 𝐑⦃T⦄.
/2 width=4/ qed-.
