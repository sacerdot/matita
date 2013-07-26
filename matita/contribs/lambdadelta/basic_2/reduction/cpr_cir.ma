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

include "basic_2/reduction/cir.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Advanced forward lemmas on context-sensitive irreducible terms ***********)

lemma cpr_fwd_cir: ∀L,T1,T2. L ⊢ T1 ➡ T2 → L ⊢ 𝐈⦃T1⦄ → T2 = T1.
#L #T1 #T2 #H elim H -L -T1 -T2
[ //
| #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 #IHV12 #H
  elim (cir_inv_delta … HLK) //
| #a * #L #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (cir_inv_bind … H) -H #HV1 #HT1 * #H destruct
    lapply (IHV1 … HV1) -IHV1 -HV1 #H destruct
    lapply (IHT1 … HT1) -IHT1 #H destruct //
  | elim (cir_inv_ib2 … H) -H /2 width=1/ /3 width=2/
  ]
| * #L #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (cir_inv_appl … H) -H #HV1 #HT1 #_
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  | elim (cir_inv_ri2 … H) /2 width=1/
  ]
| #L #V1 #T1 #T #T2 #_ #_ #_ #H
  elim (cir_inv_ri2 … H) /2 width=1/
| #L #V1 #T1 #T2 #_ #_ #H
  elim (cir_inv_ri2 … H) /2 width=1/
| #a #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H
  elim (cir_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #a #L #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (cir_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
]
qed-.
