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

include "basic_2/reduction/cix.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Advanced forward lemmas on irreducibility ********************************)

lemma cpx_fwd_cix: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃T1⦄ → T2 = T1.
#h #g #G #L #T1 #T2 #H elim H -G -L -T1 -T2
[ //
| #G #L #k #l #Hkl #H elim (cix_inv_sort … Hkl H)
| #I #G #L #K #V1 #V2 #W2 #i #HLK #_ #HVW2 #IHV12 #H
  elim (cix_inv_delta … HLK) //
| #a * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (cix_inv_bind … H) -H #HV1 #HT1 * #H destruct
    lapply (IHV1 … HV1) -IHV1 -HV1 #H destruct
    lapply (IHT1 … HT1) -IHT1 #H destruct //
  | elim (cix_inv_ib2 … H) -H /3 width=2 by or_introl, eq_f2/
  ]
| * #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (cix_inv_appl … H) -H #HV1 #HT1 #_
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  | elim (cix_inv_ri2 … H) /2 width=1 by/
  ]
| #G #L #V1 #T1 #T #T2 #_ #_ #_ #H
  elim (cix_inv_ri2 … H) /2 width=1 by or_introl/
| #G #L #V1 #T1 #T2 #_ #_ #H
  elim (cix_inv_ri2 … H) /2 width=1 by/
| #G #L #V1 #V2 #T #_ #_ #H
  elim (cix_inv_ri2 … H) /2 width=1 by/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H
  elim (cix_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #a #G #L #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (cix_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
]
qed-.
