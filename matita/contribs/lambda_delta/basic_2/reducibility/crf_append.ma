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

include "basic_2/substitution/ldrop_ldrop.ma".
include "basic_2/reducibility/crf.ma".

(* CONTEXT-SENSITIVE REDUCIBLE TERMS ****************************************)

(* advanced inversion lemmas ************************************************)
(*
lemma crf_inv_labst_last: ∀L1,T,W. L1 ⊢ 𝐑⦃T⦄ → ⇩[0, |L1|-1] L1 ≡ ⋆.ⓛW →
                          ∀L2. ⇩[|L1|-1, 1] L1 ≡ L2 → L2 ⊢ 𝐑⦃T⦄.
#L1 #T #W #H elim H -L1 -T /2 width=1/ /3 width=1/
[ #L1 #K1 #V1 #i #HLK1 #HL1 #L2 #HL12 destruct
  lapply (ldrop_fwd_ldrop2_length … HLK1) #H
  elim (le_to_or_lt_eq i (|L1|-1) ?) /2 width=1/ -H #Hi destruct [ -HL1 | - HL12 ]
  [ elim (ldrop_conf_lt … HL12 … HLK1 ?) -HLK1 -HL12 // -Hi /2 width=3/
  | lapply (ldrop_mono … HL1 … HLK1) -HL1 -HLK1 #H destruct
  ]
| #a #I #L1 #V #T #HI #_
  normalize <minus_plus_m_m #IHT #HL1 #L2 #HL12
  lapply (ldrop_fwd_ldrop2_length … HL1) #H
  lapply (ltn_to_ltO … H) -H #H
  @(crf_ib2_dx … HI) @IHT
  [ @ldrop_ldrop_lt //
  | @ldrop_skip_lt //
]
qed.


lemma crf_inv_labst_last: ∀L,T,W. ⋆.ⓛW @@ L ⊢ 𝐑⦃T⦄  → L ⊢ 𝐑⦃T⦄.
#L2 #T #H elim H -L2 -T
[ #L2 #K2 #V2 #i #HLK2 #L1 #HL12
*)
