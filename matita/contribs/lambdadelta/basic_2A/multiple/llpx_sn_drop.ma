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

include "ground/xoa/ex_4_2.ma".
include "basic_2A/substitution/drop_drop.ma".
include "basic_2A/multiple/llpx_sn_lreq.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Advanced forward lemmas **************************************************)

lemma llpx_sn_fwd_lref_dx: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 →
                           ∀I,K2,V2. ⬇[i] L2 ≡ K2.ⓑ{I}V2 →
                           i < l ∨
                           ∃∃K1,V1. ⬇[i] L1 ≡ K1.ⓑ{I}V1 & llpx_sn R 0 V1 K1 K2 &
                                    R K1 V1 V2 & l ≤ i.
#R #L1 #L2 #l #i #H #I #K2 #V2 #HLK2 elim (llpx_sn_fwd_lref … H) -H [ * || * ]
[ #_ #H elim (lt_refl_false i)
  lapply (drop_fwd_length_lt2 … HLK2) -HLK2
  /2 width=3 by lt_to_le_to_lt/ (**) (* full auto too slow *)
| /2 width=1 by or_introl/
| #I #K11 #K22 #V11 #V22 #HLK11 #HLK22 #HK12 #HV12 #Hli
  lapply (drop_mono … HLK22 … HLK2) -L2 #H destruct
  /3 width=5 by ex4_2_intro, or_intror/
]
qed-.

lemma llpx_sn_fwd_lref_sn: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 →
                           ∀I,K1,V1. ⬇[i] L1 ≡ K1.ⓑ{I}V1 →
                           i < l ∨
                           ∃∃K2,V2. ⬇[i] L2 ≡ K2.ⓑ{I}V2 & llpx_sn R 0 V1 K1 K2 &
                                    R K1 V1 V2 & l ≤ i.
#R #L1 #L2 #l #i #H #I #K1 #V1 #HLK1 elim (llpx_sn_fwd_lref … H) -H [ * || * ]
[ #H #_ elim (lt_refl_false i)
  lapply (drop_fwd_length_lt2 … HLK1) -HLK1
  /2 width=3 by lt_to_le_to_lt/ (**) (* full auto too slow *)
| /2 width=1 by or_introl/
| #I #K11 #K22 #V11 #V22 #HLK11 #HLK22 #HK12 #HV12 #Hli
  lapply (drop_mono … HLK11 … HLK1) -L1 #H destruct
  /3 width=5 by ex4_2_intro, or_intror/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma llpx_sn_inv_lref_ge_dx: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 → l ≤ i →
                              ∀I,K2,V2. ⬇[i] L2 ≡ K2.ⓑ{I}V2 →
                              ∃∃K1,V1. ⬇[i] L1 ≡ K1.ⓑ{I}V1 &
                                       llpx_sn R 0 V1 K1 K2 & R K1 V1 V2.
#R #L1 #L2 #l #i #H #Hli #I #K2 #V2 #HLK2 elim (llpx_sn_fwd_lref_dx … H … HLK2) -L2
[ #H elim (ylt_yle_false … H Hli)
| * /2 width=5 by ex3_2_intro/
]
qed-.

lemma llpx_sn_inv_lref_ge_sn: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 → l ≤ i →
                              ∀I,K1,V1. ⬇[i] L1 ≡ K1.ⓑ{I}V1 →
                              ∃∃K2,V2. ⬇[i] L2 ≡ K2.ⓑ{I}V2 &
                                       llpx_sn R 0 V1 K1 K2 & R K1 V1 V2.
#R #L1 #L2 #l #i #H #Hli #I #K1 #V1 #HLK1 elim (llpx_sn_fwd_lref_sn … H … HLK1) -L1
[ #H elim (ylt_yle_false … H Hli)
| * /2 width=5 by ex3_2_intro/
]
qed-.

lemma llpx_sn_inv_lref_ge_bi: ∀R,L1,L2,l,i. llpx_sn R l (#i) L1 L2 → l ≤ i →
                              ∀I1,I2,K1,K2,V1,V2.
                              ⬇[i] L1 ≡ K1.ⓑ{I1}V1 → ⬇[i] L2 ≡ K2.ⓑ{I2}V2 →
                              ∧∧ I1 = I2 & llpx_sn R 0 V1 K1 K2 & R K1 V1 V2.
#R #L1 #L2 #l #i #HL12 #Hli #I1 #I2 #K1 #K2 #V1 #V2 #HLK1 #HLK2
elim (llpx_sn_inv_lref_ge_sn … HL12 … HLK1) // -L1 -l
#J #Y #HY lapply (drop_mono … HY … HLK2) -L2 -i #H destruct /2 width=1 by and3_intro/
qed-.

fact llpx_sn_inv_S_aux: ∀R,L1,L2,T,l0. llpx_sn R l0 T L1 L2 → ∀l. l0 = l + 1 →
                        ∀K1,K2,I,V1,V2. ⬇[l] L1 ≡ K1.ⓑ{I}V1 → ⬇[l] L2 ≡ K2.ⓑ{I}V2 →
                        llpx_sn R 0 V1 K1 K2 → R K1 V1 V2 → llpx_sn R l T L1 L2.
#R #L1 #L2 #T #l0 #H elim H -L1 -L2 -T -l0
/2 width=1 by llpx_sn_gref, llpx_sn_free, llpx_sn_sort/
[ #L1 #L2 #l0 #i #HL12 #Hil #l #H #K1 #K2 #I #V1 #V2 #HLK1 #HLK2 #HK12 #HV12 destruct
  elim (yle_split_eq i l) /2 width=1 by llpx_sn_skip, ylt_fwd_succ2/ -HL12 -Hil
  #H destruct /2 width=9 by llpx_sn_lref/
| #I #L1 #L2 #K11 #K22 #V1 #V2 #l0 #i #Hl0i #HLK11 #HLK22 #HK12 #HV12 #_ #l #H #K1 #K2 #J #W1 #W2 #_ #_ #_ #_ destruct
  /3 width=9 by llpx_sn_lref, yle_pred_sn/
| #a #I #L1 #L2 #V #T #l0 #_ #_ #IHV #IHT #l #H #K1 #K2 #J #W1 #W2 #HLK1 #HLK2 #HK12 #HW12 destruct
  /4 width=9 by llpx_sn_bind, drop_drop/
| #I #L1 #L2 #V #T #l0 #_ #_ #IHV #IHT #l #H #K1 #K2 #J #W1 #W2 #HLK1 #HLK2 #HK12 #HW12 destruct
  /3 width=9 by llpx_sn_flat/
]
qed-.

lemma llpx_sn_inv_S: ∀R,L1,L2,T,l. llpx_sn R (l + 1) T L1 L2 →
                     ∀K1,K2,I,V1,V2. ⬇[l] L1 ≡ K1.ⓑ{I}V1 → ⬇[l] L2 ≡ K2.ⓑ{I}V2 →
                     llpx_sn R 0 V1 K1 K2 → R K1 V1 V2 → llpx_sn R l T L1 L2.
/2 width=9 by llpx_sn_inv_S_aux/ qed-.

lemma llpx_sn_inv_bind_O: ∀R. (∀L. reflexive … (R L)) →
                          ∀a,I,L1,L2,V,T. llpx_sn R 0 (ⓑ{a,I}V.T) L1 L2 →
                          llpx_sn R 0 V L1 L2 ∧ llpx_sn R 0 T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
#R #HR #a #I #L1 #L2 #V #T #H elim (llpx_sn_inv_bind … H) -H
/3 width=9 by drop_pair, conj, llpx_sn_inv_S/
qed-.

(* More advanced forward lemmas *********************************************)

lemma llpx_sn_fwd_bind_O_dx: ∀R. (∀L. reflexive … (R L)) →
                             ∀a,I,L1,L2,V,T. llpx_sn R 0 (ⓑ{a,I}V.T) L1 L2 →
                             llpx_sn R 0 T (L1.ⓑ{I}V) (L2.ⓑ{I}V).
#R #HR #a #I #L1 #L2 #V #T #H elim (llpx_sn_inv_bind_O … H) -H //
qed-.

(* Advanced properties ******************************************************)

lemma llpx_sn_bind_repl_O: ∀R,I,L1,L2,V1,V2,T. llpx_sn R 0 T (L1.ⓑ{I}V1) (L2.ⓑ{I}V2) →
                           ∀J,W1,W2. llpx_sn R 0 W1 L1 L2 → R L1 W1 W2 → llpx_sn R 0 T (L1.ⓑ{J}W1) (L2.ⓑ{J}W2).
/3 width=9 by llpx_sn_bind_repl_SO, llpx_sn_inv_S/ qed-.

lemma llpx_sn_dec: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                   ∀T,L1,L2,l. Decidable (llpx_sn R l T L1 L2).
#R #HR #T #L1 @(f2_ind … rfw … L1 T) -L1 -T
#x #IH #L1 * *
[ #k #Hx #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, llpx_sn_sort/
| #i #Hx #L2 elim (eq_nat_dec (|L1|) (|L2|))
  [ #HL12 #l elim (ylt_split i l) /3 width=1 by llpx_sn_skip, or_introl/
    #Hli elim (lt_or_ge i (|L1|)) #HiL1
    elim (lt_or_ge i (|L2|)) #HiL2 /3 width=1 by or_introl, llpx_sn_free/
    elim (drop_O1_lt (Ⓕ) … HiL2) #I2 #K2 #V2 #HLK2
    elim (drop_O1_lt (Ⓕ) … HiL1) #I1 #K1 #V1 #HLK1
    elim (eq_bind2_dec I2 I1)
    [ #H2 elim (HR K1 V1 V2) -HR
      [ #H3 elim (IH K1 V1 … K2 0) destruct
        /3 width=9 by llpx_sn_lref, drop_fwd_rfw, or_introl/
      ]
    ]
    -IH #H3 @or_intror
    #H elim (llpx_sn_fwd_lref … H) -H [1,3,4,6,7,9: * ]
    [1,3,5: /3 width=4 by lt_to_le_to_lt, lt_refl_false/
    |7,8,9: /2 width=4 by ylt_yle_false/
    ]
    #Z #Y1 #Y2 #X1 #X2 #HLY1 #HLY2 #HY12 #HX12
    lapply (drop_mono … HLY1 … HLK1) -HLY1 -HLK1
    lapply (drop_mono … HLY2 … HLK2) -HLY2 -HLK2
    #H #H0 destruct /2 width=1 by/
  ]
| #p #Hx #L2 elim (eq_nat_dec (|L1|) (|L2|)) /3 width=1 by or_introl, llpx_sn_gref/
| #a #I #V #T #Hx #L2 #l destruct
  elim (IH L1 V … L2 l) /2 width=1 by/
  elim (IH (L1.ⓑ{I}V) T … (L2.ⓑ{I}V) (↑l)) -IH /3 width=1 by or_introl, llpx_sn_bind/
  #H1 #H2 @or_intror
  #H elim (llpx_sn_inv_bind … H) -H /2 width=1 by/
| #I #V #T #Hx #L2 #l destruct
  elim (IH L1 V … L2 l) /2 width=1 by/
  elim (IH L1 T … L2 l) -IH /3 width=1 by or_introl, llpx_sn_flat/
  #H1 #H2 @or_intror
  #H elim (llpx_sn_inv_flat … H) -H /2 width=1 by/
]
-x /4 width=4 by llpx_sn_fwd_length, or_intror/
qed-.

(* Properties on relocation *************************************************)

lemma llpx_sn_lift_le: ∀R. d_liftable R →
                       ∀K1,K2,T,l0. llpx_sn R l0 T K1 K2 →
                       ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                       ∀U. ⬆[l, m] T ≡ U → l0 ≤ l → llpx_sn R l0 U L1 L2.
#R #HR #K1 #K2 #T #l0 #H elim H -K1 -K2 -T -l0
[ #K1 #K2 #l0 #k #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_sort1 … H) -X
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -l
  /2 width=1 by llpx_sn_sort/
| #K1 #K2 #l0 #i #HK12 #Hil0 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref1 … H) -H
  * #Hli #H destruct
  [ lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -l
    /2 width=1 by llpx_sn_skip/
  | elim (ylt_yle_false … Hil0) -L1 -L2 -K1 -K2 -m -Hil0
    /3 width=3 by yle_trans, yle_inj/
  ]
| #I #K1 #K2 #K11 #K22 #V1 #V2 #l0 #i #Hil0 #HK11 #HK22 #HK12 #HV12 #IHK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref1 … H) -H
  * #Hli #H destruct [ -HK12 | -IHK12 ]
  [ elim (drop_trans_lt … HLK1 … HK11) // -K1
    elim (drop_trans_lt … HLK2 … HK22) // -Hli -K2
    /3 width=18 by llpx_sn_lref/
  | lapply (drop_trans_ge_comm … HLK1 … HK11 ?) // -K1
    lapply (drop_trans_ge_comm … HLK2 … HK22 ?) // -Hli -Hl0 -K2
    /3 width=9 by llpx_sn_lref, yle_plus_dx1_trans/
  ]
| #K1 #K2 #l0 #i #HK1 #HK2 #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref1 … H) -H
  * #Hil #H destruct
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -HK12
  [ /3 width=7 by llpx_sn_free, drop_fwd_be/
  | lapply (drop_fwd_length … HLK1) -HLK1 #HLK1
    lapply (drop_fwd_length … HLK2) -HLK2 #HLK2
    @llpx_sn_free [ >HLK1 | >HLK2 ] -Hil -HLK1 -HLK2 /2 width=1 by monotonic_le_plus_r/ (**) (* explicit constructor *)
  ]
| #K1 #K2 #l0 #p #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_gref1 … H) -X
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -l -m
  /2 width=1 by llpx_sn_gref/
| #a #I #K1 #K2 #V #T #l0 #_ #_ #IHV #IHT #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_bind1 … H) -H
  #W #U #HVW #HTU #H destruct /4 width=6 by llpx_sn_bind, drop_skip, yle_succ/
| #I #K1 #K2 #V #T #l0 #_ #_ #IHV #IHT #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_flat1 … H) -H
  #W #U #HVW #HTU #H destruct /3 width=6 by llpx_sn_flat/
]
qed-.

lemma llpx_sn_lift_ge: ∀R,K1,K2,T,l0. llpx_sn R l0 T K1 K2 →
                       ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                       ∀U. ⬆[l, m] T ≡ U → l ≤ l0 → llpx_sn R (l0+m) U L1 L2.
#R #K1 #K2 #T #l0 #H elim H -K1 -K2 -T -l0
[ #K1 #K2 #l0 #k #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_sort1 … H) -X
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -l
  /2 width=1 by llpx_sn_sort/
| #K1 #K2 #l0 #i #HK12 #Hil0 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #_ elim (lift_inv_lref1 … H) -H
  * #_ #H destruct
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2
  [ /3 width=3 by llpx_sn_skip, ylt_plus_dx1_trans/
  | /3 width=3 by llpx_sn_skip, monotonic_ylt_plus_dx/
  ]
| #I #K1 #K2 #K11 #K22 #V1 #V2 #l0 #i #Hil0 #HK11 #HK22 #HK12 #HV12 #_ #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref1 … H) -H
  * #Hil #H destruct
  [ elim (ylt_yle_false … Hil0) -I -L1 -L2 -K1 -K2 -K11 -K22 -V1 -V2 -m -Hil0
    /3 width=3 by ylt_yle_trans, ylt_inj/
  | lapply (drop_trans_ge_comm … HLK1 … HK11 ?) // -K1
    lapply (drop_trans_ge_comm … HLK2 … HK22 ?) // -Hil -Hl0 -K2
    /3 width=9 by llpx_sn_lref, monotonic_yle_plus_dx/
  ]
| #K1 #K2 #l0 #i #HK1 #HK2 #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref1 … H) -H
  * #Hil #H destruct
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -HK12
  [ /3 width=7 by llpx_sn_free, drop_fwd_be/
  | lapply (drop_fwd_length … HLK1) -HLK1 #HLK1
    lapply (drop_fwd_length … HLK2) -HLK2 #HLK2
    @llpx_sn_free [ >HLK1 | >HLK2 ] -Hil -HLK1 -HLK2 /2 width=1 by monotonic_le_plus_r/ (**) (* explicit constructor *)
  ]
| #K1 #K2 #l0 #p #HK12 #L1 #L2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_gref1 … H) -X
  lapply (drop_fwd_length_eq2 … HLK1 HLK2 HK12) -K1 -K2 -l
  /2 width=1 by llpx_sn_gref/
| #a #I #K1 #K2 #V #T #l0 #_ #_ #IHV #IHT #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_bind1 … H) -H
  #W #U #HVW #HTU #H destruct /4 width=5 by llpx_sn_bind, drop_skip, yle_succ/
| #I #K1 #K2 #V #T #l0 #_ #_ #IHV #IHT #L1 #L2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_flat1 … H) -H
  #W #U #HVW #HTU #H destruct /3 width=5 by llpx_sn_flat/
]
qed-.

(* Inversion lemmas on relocation *******************************************)

lemma llpx_sn_inv_lift_le: ∀R. d_deliftable_sn R →
                           ∀L1,L2,U,l0. llpx_sn R l0 U L1 L2 →
                           ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                           ∀T. ⬆[l, m] T ≡ U → l0 ≤ l → llpx_sn R l0 T K1 K2.
#R #HR #L1 #L2 #U #l0 #H elim H -L1 -L2 -U -l0
[ #L1 #L2 #l0 #k #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_sort2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l -m
  /2 width=1 by llpx_sn_sort/
| #L1 #L2 #l0 #i #HL12 #Hil0 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2
  [ /2 width=1 by llpx_sn_skip/
  | /3 width=3 by llpx_sn_skip, yle_ylt_trans/
  ]
| #I #L1 #L2 #K11 #K22 #W1 #W2 #l0 #i #Hil0 #HLK11 #HLK22 #HK12 #HW12 #IHK12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref2 … H) -H
  * #Hil #H destruct [ -HK12 | -IHK12 ]
  [ elim (drop_conf_lt … HLK1 … HLK11) // -L1 #L1 #V1 #HKL1 #HKL11 #HVW1
    elim (drop_conf_lt … HLK2 … HLK22) // -Hil -L2 #L2 #V2 #HKL2 #HKL22 #HVW2
    elim (HR … HW12 … HKL11 … HVW1) -HR #V0 #HV0 #HV12
    lapply (lift_inj … HV0 … HVW2) -HV0 -HVW2 #H destruct
    /3 width=10 by llpx_sn_lref/
  | lapply (drop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (drop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hil0
    elim (le_inv_plus_l … Hil) -Hil /4 width=9 by llpx_sn_lref, yle_trans, yle_inj/ (**) (* slow *)
  ]
| #L1 #L2 #l0 #i #HL1 #HL2 #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (drop_fwd_length_le4 … HLK1) -HLK1
    lapply (drop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @llpx_sn_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (drop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (drop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by llpx_sn_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #l0 #p #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_gref2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l -m
  /2 width=1 by llpx_sn_gref/
| #a #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct /4 width=6 by llpx_sn_bind, drop_skip, yle_succ/
| #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=6 by llpx_sn_flat/
]
qed-.

lemma llpx_sn_inv_lift_be: ∀R,L1,L2,U,l0. llpx_sn R l0 U L1 L2 →
                           ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                           ∀T. ⬆[l, m] T ≡ U → l ≤ l0 → l0 ≤ yinj l + m → llpx_sn R l T K1 K2.
#R #L1 #L2 #U #l0 #H elim H -L1 -L2 -U -l0
[ #L1 #L2 #l0 #k #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ #_ >(lift_inv_sort2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l0 -m
  /2 width=1 by llpx_sn_sort/
| #L1 #L2 #l0 #i #HL12 #Hil0 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 #Hl0m elim (lift_inv_lref2 … H) -H
  * #Hil #H destruct
  [ lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2
    -Hil0 /3 width=1 by llpx_sn_skip, ylt_inj/
  | elim (ylt_yle_false … Hil0) -L1 -L2 -Hl0 -Hil0
    /3 width=3 by yle_trans, yle_inj/ (**) (* slow *)
  ]
| #I #L1 #L2 #K11 #K22 #W1 #W2 #l0 #i #Hil0 #HLK11 #HLK22 #HK12 #HW12 #_ #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 #Hl0m elim (lift_inv_lref2 … H) -H
  * #Hil #H destruct
  [ elim (ylt_yle_false … Hil0) -I -L1 -L2 -K11 -K22 -W1 -W2 -Hl0m -Hil0
    /3 width=3 by ylt_yle_trans, ylt_inj/
  | lapply (drop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (drop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hil0 -Hl0 -Hl0m
    elim (le_inv_plus_l … Hil) -Hil /3 width=9 by llpx_sn_lref, yle_inj/
  ]
| #L1 #L2 #l0 #i #HL1 #HL2 #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 #Hl0m elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (drop_fwd_length_le4 … HLK1) -HLK1
    lapply (drop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @llpx_sn_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (drop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (drop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by llpx_sn_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #l0 #p #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ #_ >(lift_inv_gref2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l0 -m
  /2 width=1 by llpx_sn_gref/
| #a #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 #Hl0m elim (lift_inv_bind2 … H) -H
  >commutative_plus #V #T #HVW #HTU #H destruct
  @llpx_sn_bind [ /2 width=5 by/ ] -IHW (**) (* explicit constructor *)
  @(IHU … HTU) -IHU -HTU /2 width=1 by drop_skip, yle_succ/
| #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hl0 #Hl0m elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=6 by llpx_sn_flat/
]
qed-.

lemma llpx_sn_inv_lift_ge: ∀R,L1,L2,U,l0. llpx_sn R l0 U L1 L2 →
                           ∀K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                           ∀T. ⬆[l, m] T ≡ U → yinj l + m ≤ l0 → llpx_sn R (l0-m) T K1 K2.
#R #L1 #L2 #U #l0 #H elim H -L1 -L2 -U -l0
[ #L1 #L2 #l0 #k #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_sort2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l
  /2 width=1 by llpx_sn_sort/
| #L1 #L2 #l0 #i #HL12 #Hil0 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hlml0 elim (lift_inv_lref2 … H) -H
  * #Hil #H destruct [ -Hil0 | -Hlml0 ]
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2
  [ /4 width=3 by llpx_sn_skip, yle_plus1_to_minus_inj2, ylt_yle_trans, ylt_inj/
  | elim (le_inv_plus_l … Hil) -Hil #_
    /4 width=1 by llpx_sn_skip, monotonic_ylt_minus_dx, yle_inj/
  ]
| #I #L1 #L2 #K11 #K22 #W1 #W2 #l0 #i #Hil0 #HLK11 #HLK22 #HK12 #HW12 #_ #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hlml0 elim (lift_inv_lref2 … H) -H
  * #Hil #H destruct
  [ elim (ylt_yle_false … Hil0) -I -L1 -L2 -K11 -K22 -W1 -W2 -Hil0
    /3 width=3 by yle_fwd_plus_sn1, ylt_yle_trans, ylt_inj/
  | lapply (drop_conf_ge … HLK1 … HLK11 ?) // -L1
    lapply (drop_conf_ge … HLK2 … HLK22 ?) // -L2 -Hlml0 -Hil
    /3 width=9 by llpx_sn_lref, monotonic_yle_minus_dx/
  ]
| #L1 #L2 #l0 #i #HL1 #HL2 #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hlml0 elim (lift_inv_lref2 … H) -H
  * #_ #H destruct
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12)
  [ lapply (drop_fwd_length_le4 … HLK1) -HLK1
    lapply (drop_fwd_length_le4 … HLK2) -HLK2
    #HKL2 #HKL1 #HK12 @llpx_sn_free // /2 width=3 by transitive_le/ (**) (* full auto too slow *)
  | lapply (drop_fwd_length … HLK1) -HLK1 #H >H in HL1; -H
    lapply (drop_fwd_length … HLK2) -HLK2 #H >H in HL2; -H
    /3 width=1 by llpx_sn_free, le_plus_to_minus_r/
  ]
| #L1 #L2 #l0 #p #HL12 #K1 #K2 #l #m #HLK1 #HLK2 #X #H #_ >(lift_inv_gref2 … H) -X
  lapply (drop_fwd_length_eq1 … HLK1 HLK2 HL12) -L1 -L2 -l
  /2 width=1 by llpx_sn_gref/
| #a #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hlml0 elim (lift_inv_bind2 … H) -H
  #V #T #HVW #HTU #H destruct
  @llpx_sn_bind [ /2 width=5 by/ ] -IHW (**) (* explicit constructor *)
  <yminus_succ1_inj /2 width=2 by yle_fwd_plus_sn2/
  @(IHU … HTU) -IHU -HTU /2 width=1 by drop_skip, yle_succ/
| #I #L1 #L2 #W #U #l0 #_ #_ #IHW #IHU #K1 #K2 #l #m #HLK1 #HLK2 #X #H #Hlml0 elim (lift_inv_flat2 … H) -H
  #V #T #HVW #HTU #H destruct /3 width=5 by llpx_sn_flat/
]
qed-.

(* Advanced inversion lemmas on relocation **********************************)

lemma llpx_sn_inv_lift_O: ∀R,L1,L2,U. llpx_sn R 0 U L1 L2 →
                          ∀K1,K2,m. ⬇[m] L1 ≡ K1 → ⬇[m] L2 ≡ K2 →
                          ∀T. ⬆[0, m] T ≡ U → llpx_sn R 0 T K1 K2.
/2 width=11 by llpx_sn_inv_lift_be/ qed-.

lemma llpx_sn_drop_conf_O: ∀R,L1,L2,U. llpx_sn R 0 U L1 L2 →
                           ∀K1,m. ⬇[m] L1 ≡ K1 → ∀T. ⬆[0, m] T ≡ U →
                           ∃∃K2. ⬇[m] L2 ≡ K2 & llpx_sn R 0 T K1 K2.
#R #L1 #L2 #U #HU #K1 #m #HLK1 #T #HTU elim (llpx_sn_fwd_drop_sn … HU … HLK1)
/3 width=10 by llpx_sn_inv_lift_O, ex2_intro/
qed-.

lemma llpx_sn_drop_trans_O: ∀R,L1,L2,U. llpx_sn R 0 U L1 L2 →
                            ∀K2,m. ⬇[m] L2 ≡ K2 → ∀T. ⬆[0, m] T ≡ U →
                            ∃∃K1. ⬇[m] L1 ≡ K1 & llpx_sn R 0 T K1 K2.
#R #L1 #L2 #U #HU #K2 #m #HLK2 #T #HTU elim (llpx_sn_fwd_drop_dx … HU … HLK2)
/3 width=10 by llpx_sn_inv_lift_O, ex2_intro/
qed-.

(* Inversion lemmas on negated lazy pointwise extension *********************)

lemma nllpx_sn_inv_bind: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                         ∀a,I,L1,L2,V,T,l. (llpx_sn R l (ⓑ{a,I}V.T) L1 L2 → ⊥) →
                         (llpx_sn R l V L1 L2 → ⊥) ∨ (llpx_sn R (↑l) T (L1.ⓑ{I}V) (L2.ⓑ{I}V) → ⊥).
#R #HR #a #I #L1 #L2 #V #T #l #H elim (llpx_sn_dec … HR V L1 L2 l)
/4 width=1 by llpx_sn_bind, or_intror, or_introl/
qed-.

lemma nllpx_sn_inv_flat: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                         ∀I,L1,L2,V,T,l. (llpx_sn R l (ⓕ{I}V.T) L1 L2 → ⊥) →
                         (llpx_sn R l V L1 L2 → ⊥) ∨ (llpx_sn R l T L1 L2 → ⊥).
#R #HR #I #L1 #L2 #V #T #l #H elim (llpx_sn_dec … HR V L1 L2 l)
/4 width=1 by llpx_sn_flat, or_intror, or_introl/
qed-.

lemma nllpx_sn_inv_bind_O: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                           ∀a,I,L1,L2,V,T. (llpx_sn R 0 (ⓑ{a,I}V.T) L1 L2 → ⊥) →
                           (llpx_sn R 0 V L1 L2 → ⊥) ∨ (llpx_sn R 0 T (L1.ⓑ{I}V) (L2.ⓑ{I}V) → ⊥).
#R #HR #a #I #L1 #L2 #V #T #H elim (llpx_sn_dec … HR V L1 L2 0)
/4 width=1 by llpx_sn_bind_O, or_intror, or_introl/
qed-.
