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

notation "hvbox( L ⊢ break term 46 T1 break ▶ ▶ * [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarAlt $L $T1 $d $e $T2 }.

include "basic_2/unfold/tpss_lift.ma".

(* PARALLEL UNFOLD ON TERMS *************************************************)

(* alternative definition of tpss *)
inductive tpssa: nat → nat → lenv → relation term ≝
| tpssa_atom : ∀L,I,d,e. tpssa d e L (⓪{I}) (⓪{I})
| tpssa_subst: ∀L,K,V1,V2,W2,i,d,e. d ≤ i → i < d + e →
               ⇩[0, i] L ≡ K. ⓓV1 → tpssa 0 (d + e - i - 1) K V1 V2 →
               ⇧[0, i + 1] V2 ≡ W2 → tpssa d e L (#i) W2
| tpssa_bind : ∀L,a,I,V1,V2,T1,T2,d,e.
               tpssa d e L V1 V2 → tpssa (d + 1) e (L. ⓑ{I} V2) T1 T2 →
               tpssa d e L (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| tpssa_flat : ∀L,I,V1,V2,T1,T2,d,e.
               tpssa d e L V1 V2 → tpssa d e L T1 T2 →
               tpssa d e L (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
.

interpretation "parallel unfold (term) alternative"
   'PSubstStarAlt L T1 d e T2 = (tpssa d e L T1 T2).

(* Basic properties *********************************************************)

lemma tpssa_lsubr_trans: ∀L1,T1,T2,d,e. L1 ⊢ T1 ▶▶* [d, e] T2 →
                         ∀L2. L2 ⊑ [d, e] L1 → L2 ⊢ T1 ▶▶* [d, e] T2.
#L1 #T1 #T2 #d #e #H elim H -L1 -T1 -T2 -d -e
[ //
| #L1 #K1 #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (ldrop_lsubr_ldrop2_abbr … HL12 … HLK1 ? ?) -HL12 -HLK1 // /3 width=6/
| /4 width=1/
| /3 width=1/
]
qed.

lemma tpssa_refl: ∀T,L,d,e. L ⊢ T ▶▶* [d, e] T.
#T elim T -T //
#I elim I -I /2 width=1/
qed.

lemma tpssa_tps_trans: ∀L,T1,T,d,e. L ⊢ T1 ▶▶* [d, e] T →
                       ∀T2. L ⊢ T ▶ [d, e] T2 → L ⊢ T1 ▶▶* [d, e] T2.
#L #T1 #T #d #e #H elim H -L -T1 -T -d -e
[ #L #I #d #e #X #H
  elim (tps_inv_atom1 … H) -H // * /2 width=6/
| #L #K #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK #_ #HVW2 #IHV12 #T2 #H
  lapply (ldrop_fwd_ldrop2 … HLK) #H0LK
  lapply (tps_weak … H 0 (d+e) ? ?) -H // #H
  elim (tps_inv_lift1_be … H … H0LK … HVW2 ? ?) -H -H0LK -HVW2 // /3 width=6/
| #L #a #I #V1 #V #T1 #T #d #e #_ #_ #IHV1 #IHT1 #X #H
  elim (tps_inv_bind1 … H) -H #V2 #T2 #HV2 #HT2 #H destruct
  lapply (tps_lsubr_trans … HT2 (L.ⓑ{I}V) ?) -HT2 /2 width=1/ #HT2
  lapply (IHV1 … HV2) -IHV1 -HV2 #HV12
  lapply (IHT1 … HT2) -IHT1 -HT2 #HT12
  lapply (tpssa_lsubr_trans … HT12 (L.ⓑ{I}V2) ?) -HT12 /2 width=1/
| #L #I #V1 #V #T1 #T #d #e #_ #_ #IHV1 #IHT1 #X #H
  elim (tps_inv_flat1 … H) -H #V2 #T2 #HV2 #HT2 #H destruct /3 width=1/
]
qed.

lemma tpss_tpssa: ∀L,T1,T2,d,e. L ⊢ T1 ▶* [d, e] T2 → L ⊢ T1 ▶▶* [d, e] T2.
#L #T1 #T2 #d #e #H @(tpss_ind … H) -T2 // /2 width=3/
qed.

(* Basic inversion lemmas ***************************************************)

lemma tpssa_tpss: ∀L,T1,T2,d,e. L ⊢ T1 ▶▶* [d, e] T2 → L ⊢ T1 ▶* [d, e] T2.
#L #T1 #T2 #d #e #H elim H -L -T1 -T2 -d -e // /2 width=6/
qed-.

lemma tpss_ind_alt: ∀R:nat→nat→lenv→relation term.
                    (∀L,I,d,e. R d e L (⓪{I}) (⓪{I})) →
                    (∀L,K,V1,V2,W2,i,d,e. d ≤ i → i < d + e →
                     ⇩[O, i] L ≡ K.ⓓV1 → K ⊢ V1 ▶* [O, d + e - i - 1] V2 →
                     ⇧[O, i + 1] V2 ≡ W2 → R O (d+e-i-1) K V1 V2 → R d e L (#i) W2
                    ) →
                    (∀L,a,I,V1,V2,T1,T2,d,e. L ⊢ V1 ▶* [d, e] V2 →
                     L.ⓑ{I}V2 ⊢ T1 ▶* [d + 1, e] T2 → R d e L V1 V2 →
                     R (d+1) e (L.ⓑ{I}V2) T1 T2 → R d e L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
                    ) →
                    (∀L,I,V1,V2,T1,T2,d,e. L ⊢ V1 ▶* [d, e] V2 →
                     L ⊢ T1 ▶* [d, e] T2 → R d e L V1 V2 →
                     R d e L T1 T2 → R d e L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
                    ) →
                    ∀d,e,L,T1,T2. L ⊢ T1 ▶* [d, e] T2 → R d e L T1 T2.
#R #H1 #H2 #H3 #H4 #d #e #L #T1 #T2 #H elim (tpss_tpssa … H) -L -T1 -T2 -d -e
// /3 width=1 by tpssa_tpss/ /3 width=7 by tpssa_tpss/
qed-.
