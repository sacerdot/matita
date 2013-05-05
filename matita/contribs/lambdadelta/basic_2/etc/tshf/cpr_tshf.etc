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

include "basic_2/grammar/tshf.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Forward lemmas on same head forms for terms ******************************)

lemma cpr_fwd_tshf1: ∀L,T1,T2. L ⊢ T1 ➡ T2 → T1 ≈ T1 →
                     T2 ≈ T1 ∨ (L = ⋆ → ⊥).
#L #T1 #T2 #H elim H -L -T1 -T2
[ /2 width=1/
| #L #K #V1 #V2 #W2 #i #HLK #_ #_ #_ #_
  @or_intror #H destruct
  lapply (ldrop_inv_atom1 … HLK) -HLK #H destruct
| #a #I #L #V1 #V2 #T1 #T2 #_ #_ #_ #_ #H
  elim (tshf_inv_bind1 … H) -H #W2 #U2 #H1 * #H2 destruct /2 width=1/
| #I #L #V1 #V2 #T1 #T2 #_ #_ #_ #IHT12 #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #HT1U2 #HT1 #_ #H1 #H2 destruct
  lapply (IHT12 HT1U2) -IHT12 -HT1U2 * #HUT2 /3 width=1/
  lapply (simple_tshf_repl_sn … HUT2 HT1) /3 width=1/
| #L #V #T #T1 #T2 #_ #_ #_ #H
  elim (tshf_inv_bind1 … H) -H #W2 #U2 #H1 * #H2 destruct
| #L #V #T1 #T2 #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #_ #_ #_ #H destruct
| #a #L #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #W2 #U2 #_ #H
  elim (simple_inv_bind … H)
| #a #L #V2 #V1 #V #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (tshf_inv_flat1 … H) -H #U1 #U2 #_ #H
  elim (simple_inv_bind … H)
]
qed-.
