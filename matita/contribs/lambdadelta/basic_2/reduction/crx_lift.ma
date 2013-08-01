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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/reduction/crx.ma".

(* CONTEXT-SENSITIVE EXTENDED REDUCIBLE TERMS *******************************)

(* Properties on relocation *************************************************)

lemma crx_lift: ∀h,g,K,T. ⦃h, K⦄ ⊢ 𝐑[h, g]⦃T⦄ → ∀L,d,e. ⇩[d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃U⦄.
#h #g #K #T #H elim H -K -T
[ #K #k #l #Hkl #L #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X /2 width=2/
| #I #K #K0 #V #i #HK0 #L #d #e #HLK #X #H
  elim (lift_inv_lref1 … H) -H * #Hid #H destruct
  [ elim (ldrop_trans_lt … HLK … HK0) -K // /2 width=4/
  | lapply (ldrop_trans_ge … HLK … HK0 ?) -K // /2 width=4/
  ]
| #K #V #T #_ #IHV #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #_ #H destruct /3 width=4/
| #K #V #T #_ #IHT #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #_ #HTU #H destruct /3 width=4/
| #I #K #V #T #HI #L #d #e #_ #X #H
  elim (lift_fwd_pair1 … H) -H #W #U #_ #H destruct /2 width=1/
| #a #I #K #V #T #HI #_ #IHV #L #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #_ #H destruct /3 width=4/
| #a #I #K #V #T #HI #_ #IHT #L #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct /4 width=4/
| #a #K #V #V0 #T #L #d #e #_ #X #H
  elim (lift_inv_flat1 … H) -H #W #X0 #_ #H0 #H destruct
  elim (lift_inv_bind1 … H0) -H0 #W0 #U #_ #_ #H0 destruct /2 width=1/
| #a #K #V #V0 #T #L #d #e #_ #X #H
  elim (lift_inv_flat1 … H) -H #W #X0 #_ #H0 #H destruct
  elim (lift_inv_bind1 … H0) -H0 #W0 #U #_ #_ #H0 destruct /2 width=1/
]
qed.

lemma crx_inv_lift: ∀h,g,L,U. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃U⦄ → ∀K,d,e. ⇩[d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃h, K⦄ ⊢ 𝐑[h, g]⦃T⦄.
#h #g #L #U #H elim H -L -U
[ #L #k #l #Hkl #K #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X /2 width=2/
| #I #L #L0 #W #i #HK0 #K #d #e #HLK #X #H
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ elim (ldrop_conf_lt … HLK … HK0) -L // /2 width=4/
  | lapply (ldrop_conf_ge … HLK … HK0 ?) -L // /2 width=4/
  ]
| #L #W #U #_ #IHW #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #_ #H destruct /3 width=4/
| #L #W #U #_ #IHU #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #_ #HTU #H destruct /3 width=4/
| #I #L #W #U #HI #K #d #e #_ #X #H
  elim (lift_fwd_pair2 … H) -H #V #T #_ #H destruct /2 width=1/
| #a #I #L #W #U #HI #_ #IHW #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #_ #H destruct /3 width=4/
| #a #I #L #W #U #HI #_ #IHU #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct /4 width=4/
| #a #L #W #W0 #U #K #d #e #_ #X #H
  elim (lift_inv_flat2 … H) -H #V #X0 #_ #H0 #H destruct
  elim (lift_inv_bind2 … H0) -H0 #V0 #T #_ #_ #H0 destruct /2 width=1/
| #a #L #W #W0 #U #K #d #e #_ #X #H
  elim (lift_inv_flat2 … H) -H #V #X0 #_ #H0 #H destruct
  elim (lift_inv_bind2 … H0) -H0 #V0 #T #_ #_ #H0 destruct /2 width=1/
]
qed.
