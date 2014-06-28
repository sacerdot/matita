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

include "basic_2/substitution/drop_drop.ma".
include "basic_2/reduction/crr.ma".

(* REDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION **************************)

(* Properties on relocation *************************************************)

lemma crr_lift: ∀G,K,T. ⦃G, K⦄ ⊢ ➡ 𝐑⦃T⦄ → ∀L,s,d,e. ⇩[s, d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ ➡ 𝐑⦃U⦄.
#G #K #T #H elim H -K -T
[ #K #K0 #V #i #HK0 #L #s #d #e #HLK #X #H
  elim (lift_inv_lref1 … H) -H * #Hid #H destruct
  [ elim (drop_trans_lt … HLK … HK0) -K /2 width=4 by crr_delta/
  | lapply (drop_trans_ge … HLK … HK0 ?) -K /3 width=4 by crr_delta, drop_inv_gen/
  ]
| #K #V #T #_ #IHV #L #s #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #_ #H destruct /3 width=5 by crr_appl_sn/
| #K #V #T #_ #IHT #L #s #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #_ #HTU #H destruct /3 width=5 by crr_appl_dx/
| #I #K #V #T #HI #L #s #d #e #_ #X #H
  elim (lift_fwd_pair1 … H) -H #W #U #_ #H destruct /2 width=1 by crr_ri2/
| #a #I #K #V #T #HI #_ #IHV #L #s #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #_ #H destruct /3 width=5 by crr_ib2_sn/
| #a #I #K #V #T #HI #_ #IHT #L #s #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct /4 width=5 by crr_ib2_dx, drop_skip/
| #a #K #V #V0 #T #L #s #d #e #_ #X #H
  elim (lift_inv_flat1 … H) -H #W #X0 #_ #H0 #H destruct
  elim (lift_inv_bind1 … H0) -H0 #W0 #U #_ #_ #H0 destruct /2 width=1 by crr_beta/
| #a #K #V #V0 #T #L #s #d #e #_ #X #H
  elim (lift_inv_flat1 … H) -H #W #X0 #_ #H0 #H destruct
  elim (lift_inv_bind1 … H0) -H0 #W0 #U #_ #_ #H0 destruct /2 width=1 by crr_theta/
]
qed.

lemma crr_inv_lift: ∀G,L,U. ⦃G, L⦄ ⊢ ➡ 𝐑⦃U⦄ → ∀K,s,d,e. ⇩[s, d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ ➡ 𝐑⦃T⦄.
#G #L #U #H elim H -L -U
[ #L #L0 #W #i #HK0 #K #s #d #e #HLK #X #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (drop_conf_lt … HLK … HK0) -L /2 width=4 by crr_delta/
  | lapply (drop_conf_ge … HLK … HK0 ?) -L /2 width=4 by crr_delta/
  ]
| #L #W #U #_ #IHW #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #_ #H destruct /3 width=5 by crr_appl_sn/
| #L #W #U #_ #IHU #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #_ #HTU #H destruct /3 width=5 by crr_appl_dx/
| #I #L #W #U #HI #K #s #d #e #_ #X #H
  elim (lift_fwd_pair2 … H) -H #V #T #_ #H destruct /2 width=1 by crr_ri2/
| #a #I #L #W #U #HI #_ #IHW #K #s #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #_ #H destruct /3 width=5 by crr_ib2_sn/
| #a #I #L #W #U #HI #_ #IHU #K #s #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct /4 width=5 by crr_ib2_dx, drop_skip/
| #a #L #W #W0 #U #K #s #d #e #_ #X #H
  elim (lift_inv_flat2 … H) -H #V #X0 #_ #H0 #H destruct
  elim (lift_inv_bind2 … H0) -H0 #V0 #T #_ #_ #H0 destruct /2 width=1 by crr_beta/
| #a #L #W #W0 #U #K #s #d #e #_ #X #H
  elim (lift_inv_flat2 … H) -H #V #X0 #_ #H0 #H destruct
  elim (lift_inv_bind2 … H0) -H0 #V0 #T #_ #_ #H0 destruct /2 width=1 by crr_theta/
]
qed-.
