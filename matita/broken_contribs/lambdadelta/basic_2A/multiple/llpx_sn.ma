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

include "ground/xoa/ex_5_5.ma".
include "ground/ynat/ynat_plus.ma".
include "basic_2A/substitution/drop.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

inductive llpx_sn (R:relation3 lenv term term): relation4 ynat term lenv lenv ≝
| llpx_sn_sort: ∀L1,L2,l,k. |L1| = |L2| → llpx_sn R l (⋆k) L1 L2
| llpx_sn_skip: ∀L1,L2,l,i. |L1| = |L2| → yinj i < l → llpx_sn R l (#i) L1 L2
| llpx_sn_lref: ∀I,L1,L2,K1,K2,V1,V2,l,i. l ≤ yinj i →
                ⬇[i] L1 ≡ K1.ⓑ{I}V1 → ⬇[i] L2 ≡ K2.ⓑ{I}V2 →
                llpx_sn R (yinj 0) V1 K1 K2 → R K1 V1 V2 → llpx_sn R l (#i) L1 L2
| llpx_sn_free: ∀L1,L2,l,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → llpx_sn R l (#i) L1 L2
| llpx_sn_gref: ∀L1,L2,l,p. |L1| = |L2| → llpx_sn R l (§p) L1 L2
| llpx_sn_bind: ∀a,I,L1,L2,V,T,l.
                llpx_sn R l V L1 L2 → llpx_sn R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
                llpx_sn R l (ⓑ{a,I}V.T) L1 L2
| llpx_sn_flat: ∀I,L1,L2,V,T,l.
                llpx_sn R l V L1 L2 → llpx_sn R l T L1 L2 → llpx_sn R l (ⓕ{I}V.T) L1 L2
.

(* Basic inversion lemmas ***************************************************)

fact llpx_sn_inv_bind_aux: ∀R,L1,L2,X,l. llpx_sn R l X L1 L2 →
                           ∀a,I,V,T. X = ⓑ{a,I}V.T →
                           llpx_sn R l V L1 L2 ∧ llpx_sn R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
#R #L1 #L2 #X #l * -L1 -L2 -X -l
[ #L1 #L2 #l #k #_ #b #J #W #U #H destruct
| #L1 #L2 #l #i #_ #_ #b #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V1 #V2 #l #i #_ #_ #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #l #i #_ #_ #_ #b #J #W #U #H destruct
| #L1 #L2 #l #p #_ #b #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #l #HV #HT #b #J #W #U #H destruct /2 width=1 by conj/
| #I #L1 #L2 #V #T #l #_ #_ #b #J #W #U #H destruct
]
qed-.

lemma llpx_sn_inv_bind: ∀R,a,I,L1,L2,V,T,l. llpx_sn R l (ⓑ{a,I}V.T) L1 L2 →
                        llpx_sn R l V L1 L2 ∧ llpx_sn R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
/2 width=4 by llpx_sn_inv_bind_aux/ qed-.

fact llpx_sn_inv_flat_aux: ∀R,L1,L2,X,l. llpx_sn R l X L1 L2 →
                           ∀I,V,T. X = ⓕ{I}V.T →
                           llpx_sn R l V L1 L2 ∧ llpx_sn R l T L1 L2.
#R #L1 #L2 #X #l * -L1 -L2 -X -l
[ #L1 #L2 #l #k #_ #J #W #U #H destruct
| #L1 #L2 #l #i #_ #_ #J #W #U #H destruct
| #I #L1 #L2 #K1 #K2 #V1 #V2 #l #i #_ #_ #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #l #i #_ #_ #_ #J #W #U #H destruct
| #L1 #L2 #l #p #_ #J #W #U #H destruct
| #a #I #L1 #L2 #V #T #l #_ #_ #J #W #U #H destruct
| #I #L1 #L2 #V #T #l #HV #HT #J #W #U #H destruct /2 width=1 by conj/
]
qed-.

lemma llpx_sn_inv_flat: ∀R,I,L1,L2,V,T,l. llpx_sn R l (ⓕ{I}V.T) L1 L2 →
                        llpx_sn R l V L1 L2 ∧ llpx_sn R l T L1 L2.
/2 width=4 by llpx_sn_inv_flat_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma llpx_sn_fwd_length: ∀R,L1,L2,T,l. llpx_sn R l T L1 L2 → |L1| = |L2|.
#R #L1 #L2 #T #l #H elim H -L1 -L2 -T -l //
#I #L1 #L2 #K1 #K2 #V1 #V2 #l #i #_ #HLK1 #HLK2 #_ #_ #HK12
lapply (drop_fwd_length … HLK1) -HLK1
lapply (drop_fwd_length … HLK2) -HLK2
normalize //
qed-.

lemma llpx_sn_fwd_drop_sn: ∀R,L1,L2,T,l. llpx_sn R l T L1 L2 →
                            ∀K1,i. ⬇[i] L1 ≡ K1 → ∃K2. ⬇[i] L2 ≡ K2.
#R #L1 #L2 #T #l #H #K1 #i #HLK1 lapply (llpx_sn_fwd_length … H) -H
#HL12 lapply (drop_fwd_length_le2 … HLK1) -HLK1 /2 width=1 by drop_O1_le/
qed-.

lemma llpx_sn_fwd_drop_dx: ∀R,L1,L2,T,l. llpx_sn R l T L1 L2 →
                            ∀K2,i. ⬇[i] L2 ≡ K2 → ∃K1. ⬇[i] L1 ≡ K1.
#R #L1 #L2 #T #l #H #K2 #i #HLK2 lapply (llpx_sn_fwd_length … H) -H
#HL12 lapply (drop_fwd_length_le2 … HLK2) -HLK2 /2 width=1 by drop_O1_le/
qed-.

fact llpx_sn_fwd_lref_aux: ∀R,L1,L2,X,l. llpx_sn R l X L1 L2 → ∀i. X = #i →
                           ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                            | yinj i < l
                            | ∃∃I,K1,K2,V1,V2. ⬇[i] L1 ≡ K1.ⓑ{I}V1 &
                                               ⬇[i] L2 ≡ K2.ⓑ{I}V2 &
                                               llpx_sn R (yinj 0) V1 K1 K2 &
                                               R K1 V1 V2 & l ≤ yinj i.
#R #L1 #L2 #X #l * -L1 -L2 -X -l
[ #L1 #L2 #l #k #_ #j #H destruct
| #L1 #L2 #l #i #_ #Hil #j #H destruct /2 width=1 by or3_intro1/
| #I #L1 #L2 #K1 #K2 #V1 #V2 #l #i #Hli #HLK1 #HLK2 #HK12 #HV12 #j #H destruct
  /3 width=9 by or3_intro2, ex5_5_intro/
| #L1 #L2 #l #i #HL1 #HL2 #_ #j #H destruct /3 width=1 by or3_intro0, conj/
| #L1 #L2 #l #p #_ #j #H destruct
| #a #I #L1 #L2 #V #T #l #_ #_ #j #H destruct
| #I #L1 #L2 #V #T #l #_ #_ #j #H destruct
]
qed-.

lemma llpx_sn_fwd_lref: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 →
                        ∨∨ |L1| ≤ i ∧ |L2| ≤ i
                         | yinj i < l
                         | ∃∃I,K1,K2,V1,V2. ⬇[i] L1 ≡ K1.ⓑ{I}V1 &
                                            ⬇[i] L2 ≡ K2.ⓑ{I}V2 &
                                            llpx_sn R (yinj 0) V1 K1 K2 &
                                            R K1 V1 V2 & l ≤ yinj i.
/2 width=3 by llpx_sn_fwd_lref_aux/ qed-.

lemma llpx_sn_fwd_bind_sn: ∀R,a,I,L1,L2,V,T,l. llpx_sn R l (ⓑ{a,I}V.T) L1 L2 →
                           llpx_sn R l V L1 L2.
#R #a #I #L1 #L2 #V #T #l #H elim (llpx_sn_inv_bind … H) -H //
qed-.

lemma llpx_sn_fwd_bind_dx: ∀R,a,I,L1,L2,V,T,l. llpx_sn R l (ⓑ{a,I}V.T) L1 L2 →
                           llpx_sn R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
#R #a #I #L1 #L2 #V #T #l #H elim (llpx_sn_inv_bind … H) -H //
qed-.

lemma llpx_sn_fwd_flat_sn: ∀R,I,L1,L2,V,T,l. llpx_sn R l (ⓕ{I}V.T) L1 L2 →
                           llpx_sn R l V L1 L2.
#R #I #L1 #L2 #V #T #l #H elim (llpx_sn_inv_flat … H) -H //
qed-.

lemma llpx_sn_fwd_flat_dx: ∀R,I,L1,L2,V,T,l. llpx_sn R l (ⓕ{I}V.T) L1 L2 →
                           llpx_sn R l T L1 L2.
#R #I #L1 #L2 #V #T #l #H elim (llpx_sn_inv_flat … H) -H //
qed-.

lemma llpx_sn_fwd_pair_sn: ∀R,I,L1,L2,V,T,l. llpx_sn R l (②{I}V.T) L1 L2 →
                           llpx_sn R l V L1 L2.
#R * /2 width=4 by llpx_sn_fwd_flat_sn, llpx_sn_fwd_bind_sn/
qed-.

(* Basic properties *********************************************************)

lemma llpx_sn_refl: ∀R. (∀L. reflexive … (R L)) → ∀T,L,l. llpx_sn R l T L L.
#R #HR #T #L @(f2_ind … rfw … L T) -L -T
#x #IH #L * * /3 width=1 by llpx_sn_sort, llpx_sn_gref, llpx_sn_bind, llpx_sn_flat/
#i #Hx elim (lt_or_ge i (|L|)) /2 width=1 by llpx_sn_free/
#HiL #l elim (ylt_split i l) /2 width=1 by llpx_sn_skip/
elim (drop_O1_lt … HiL) -HiL destruct /4 width=9 by llpx_sn_lref, drop_fwd_rfw/
qed-.

lemma llpx_sn_Y: ∀R,T,L1,L2. |L1| = |L2| → llpx_sn R (∞) T L1 L2.
#R #T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#x #IH #L1 * * /3 width=1 by llpx_sn_sort, llpx_sn_skip, llpx_sn_gref, llpx_sn_flat/
#a #I #V1 #T1 #Hx #L2 #HL12
@llpx_sn_bind /2 width=1 by/ (**) (* explicit constructor *)
@IH -IH // normalize /2 width=1 by eq_f2/
qed-.

lemma llpx_sn_ge_up: ∀R,L1,L2,U,lt. llpx_sn R lt U L1 L2 → ∀T,l,m. ⬆[l, m] T ≡ U →
                     lt ≤ l + m → llpx_sn R l U L1 L2.
#R #L1 #L2 #U #lt #H elim H -L1 -L2 -U -lt
[ #L1 #L2 #lt #k #HL12 #X #l #m #H #_ >(lift_inv_sort2 … H) -H /2 width=1 by llpx_sn_sort/
| #L1 #L2 #lt #i #HL12 #Hilt #X #l #m #H #Hltlm
  elim (lift_inv_lref2 … H) -H * #Hil #H destruct /3 width=1 by llpx_sn_skip, ylt_inj/ -HL12
  elim (ylt_yle_false … Hilt) -Hilt
  @(yle_trans … Hltlm) /2 width=1 by yle_inj/ (**) (* full auto too slow 11s *)
| #I #L1 #L2 #K1 #K2 #W1 #W2 #lt #i #Hlti #HLK1 #HLK2 #HW1 #HW12 #_ #X #l #m #H #_
  elim (lift_inv_lref2 … H) -H * #Hil #H destruct
  [ lapply (llpx_sn_fwd_length … HW1) -HW1 #HK12
    lapply (drop_fwd_length … HLK1) lapply (drop_fwd_length … HLK2)
    normalize in ⊢ (%→%→?); -I -W1 -W2 -lt /3 width=1 by llpx_sn_skip, ylt_inj/
  | /4 width=9 by llpx_sn_lref, yle_inj, le_plus_b/
  ]
| /2 width=1 by llpx_sn_free/
| #L1 #L2 #lt #p #HL12 #X #l #m #H #_ >(lift_inv_gref2 … H) -H /2 width=1 by llpx_sn_gref/
| #a #I #L1 #L2 #W #U #lt #_ #_ #IHV #IHT #X #l #m #H #Hltlm destruct
  elim (lift_inv_bind2 … H) -H #V #T #HVW >commutative_plus #HTU #H destruct
  @(llpx_sn_bind) /2 width=4 by/ (**) (* full auto fails *)
  @(IHT … HTU) /2 width=1 by yle_succ/
| #I #L1 #L2 #W #U #lt #_ #_ #IHV #IHT #X #l #m #H #Hltlm destruct
  elim (lift_inv_flat2 … H) -H #HVW #HTU #H destruct
  /3 width=4 by llpx_sn_flat/
]
qed-.

(**) (* the minor premise comes first *)
lemma llpx_sn_ge: ∀R,L1,L2,T,l1,l2. l1 ≤ l2 →
                  llpx_sn R l1 T L1 L2 → llpx_sn R l2 T L1 L2.
#R #L1 #L2 #T #l1 #l2 * -l1 -l2 (**) (* destructed yle *)
/3 width=6 by llpx_sn_ge_up, llpx_sn_Y, llpx_sn_fwd_length, yle_inj/
qed-.

lemma llpx_sn_bind_O: ∀R,a,I,L1,L2,V,T. llpx_sn R 0 V L1 L2 →
                      llpx_sn R 0 T (L1.ⓑ{I}V) (L2.ⓑ{I}V) →
                      llpx_sn R 0 (ⓑ{a,I}V.T) L1 L2.
/3 width=3 by llpx_sn_ge, llpx_sn_bind/ qed-.

lemma llpx_sn_co: ∀R1,R2. (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
                  ∀L1,L2,T,l. llpx_sn R1 l T L1 L2 → llpx_sn R2 l T L1 L2.
#R1 #R2 #HR12 #L1 #L2 #T #l #H elim H -L1 -L2 -T -l
/3 width=9 by llpx_sn_sort, llpx_sn_skip, llpx_sn_lref, llpx_sn_free, llpx_sn_gref, llpx_sn_bind, llpx_sn_flat/
qed-.
