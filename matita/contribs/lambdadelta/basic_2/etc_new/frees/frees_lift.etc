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

include "ground_2/ynat/ynat_max.ma".
include "basic_2/substitution/drop_drop.ma".
include "basic_2/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

lemma frees_dec: ∀L,U,l,i. Decidable (frees l L U i).
#L #U @(f2_ind … rfw … L U) -L -U
#x #IH #L * *
[ -IH /3 width=5 by frees_inv_sort, or_intror/
| #j #Hx #l #i elim (ylt_split_eq i j) #Hji
  [ -x @or_intror #H elim (ylt_yle_false … Hji)
    lapply (frees_inv_lref_ge … H ?) -L -l /2 width=1 by ylt_fwd_le/
  | -x /2 width=1 by or_introl/
  | elim (ylt_split j l) #Hli
    [ -x @or_intror #H elim (ylt_yle_false … Hji)
      lapply (frees_inv_lref_skip … H ?) -L //
    | elim (lt_or_ge j (|L|)) #Hj
      [ elim (drop_O1_lt (Ⓕ) L j) // -Hj #I #K #W #HLK destruct
        elim (IH K W … 0 (i-j-1)) -IH [1,3: /3 width=5 by frees_lref_be, drop_fwd_rfw, or_introl/ ] #HnW
        @or_intror #H elim (frees_inv_lref_lt … H) // #Z #Y #X #_ #HLY -l
        lapply (drop_mono … HLY … HLK) -L #H destruct /2 width=1 by/  
      | -x @or_intror #H elim (ylt_yle_false … Hji)
        lapply (frees_inv_lref_free … H ?) -l //
      ]
    ]
  ]
| -IH /3 width=5 by frees_inv_gref, or_intror/
| #a #I #W #U #Hx #l #i destruct
  elim (IH L W … l i) [1,3: /3 width=1 by frees_bind_sn, or_introl/ ] #HnW
  elim (IH (L.ⓑ{I}W) U … (⫯l) (i+1)) -IH [1,3: /3 width=1 by frees_bind_dx, or_introl/ ] #HnU
  @or_intror #H elim (frees_inv_bind … H) -H /2 width=1 by/
| #I #W #U #Hx #l #i destruct
  elim (IH L W … l i) [1,3: /3 width=1 by frees_flat_sn, or_introl/ ] #HnW
  elim (IH L U … l i) -IH [1,3: /3 width=1 by frees_flat_dx, or_introl/ ] #HnU
  @or_intror #H elim (frees_inv_flat … H) -H /2 width=1 by/
]
qed-.

lemma frees_S: ∀L,U,l,i. L ⊢ i ϵ 𝐅*[yinj l]⦃U⦄ → ∀I,K,W. ⬇[l] L ≡ K.ⓑ{I}W →
               (K ⊢ ⫰(i-l) ϵ 𝐅*[0]⦃W⦄ → ⊥) → L ⊢ i ϵ 𝐅*[⫯l]⦃U⦄.
#L #U #l #i #H elim (frees_inv … H) -H /3 width=2 by frees_eq/
* #I #K #W #j #Hlj #Hji #HnU #HLK #HW #I0 #K0 #W0 #HLK0 #HnW0
lapply (yle_inv_inj … Hlj) -Hlj #Hlj
elim (le_to_or_lt_eq … Hlj) -Hlj
[ -I0 -K0 -W0 /3 width=9 by frees_be, yle_inj/
| -Hji -HnU #H destruct
  lapply (drop_mono … HLK0 … HLK) #H destruct -I
  elim HnW0 -L -U -HnW0 //
]
qed.

(* Note: lemma 1250 *)
lemma frees_bind_dx_O: ∀a,I,L,W,U,i. L.ⓑ{I}W ⊢ ⫯i ϵ 𝐅*[0]⦃U⦄ →
                       L ⊢ i ϵ 𝐅*[0]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #i #HU elim (frees_dec L W 0 i)
/4 width=5 by frees_S, frees_bind_dx, frees_bind_sn/
qed.

(* Properties on relocation *************************************************)

lemma frees_lift_ge: ∀K,T,l,i. K ⊢ i ϵ𝐅*[l]⦃T⦄ →
                     ∀L,s,l0,m0. ⬇[s, l0, m0] L ≡ K →
                     ∀U. ⬆[l0, m0] T ≡ U → l0 ≤ i →
                     L ⊢ i+m0 ϵ 𝐅*[l]⦃U⦄.
#K #T #l #i #H elim H -K -T -l -i
[ #K #T #l #i #HnT #L #s #l0 #m0 #_ #U #HTU #Hl0i -K -s
  @frees_eq #X #HXU elim (lift_div_le … HTU … HXU) -U /2 width=2 by/
| #I #K #K0 #T #V #l #i #j #Hlj #Hji #HnT #HK0 #HV #IHV #L #s #l0 #m0 #HLK #U #HTU #Hl0i
  elim (ylt_split j l0) #H0
  [ elim (drop_trans_lt … HLK … HK0) // -K #L0 #W #HL0 >yminus_SO2 #HLK0 #HVW
    @(frees_be … HL0) -HL0 -HV /3 width=3 by ylt_plus_dx2_trans/
    [ lapply (ylt_fwd_lt_O1 … H0) #H1
      #X #HXU <(ymax_pre_sn l0 1) in HTU; /2 width=1 by ylt_fwd_le_succ1/ #HTU
      <(ylt_inv_O1 l0) in H0; // -H1 #H0
      elim (lift_div_le … HXU … HTU ?) -U /2 width=2 by ylt_fwd_succ2/
    | >yplus_minus_comm_inj /2 width=1 by ylt_fwd_le/
      <yplus_pred1 /4 width=5 by monotonic_yle_minus_dx, yle_pred, ylt_to_minus/
    ]
  | lapply (drop_trans_ge … HLK … HK0 ?) // -K #HLK0
    lapply (drop_inv_gen … HLK0) >commutative_plus -HLK0 #HLK0
    @(frees_be … HLK0) -HLK0 -IHV
    /2 width=1 by monotonic_ylt_plus_dx, yle_plus_dx1_trans/
    [ #X <yplus_inj #HXU elim (lift_div_le … HTU … HXU) -U /2 width=2 by/
    | <yplus_minus_assoc_comm_inj //
    ]
  ]
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma frees_inv_lift_be: ∀L,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                         ∀K,s,l0,m0. ⬇[s, l0, m0+1] L ≡ K →
                         ∀T. ⬆[l0, m0+1] T ≡ U → l0 ≤ i → i ≤ l0 + m0 → ⊥.
#L #U #l #i #H elim H -L -U -l -i
[ #L #U #l #i #HnU #K #s #l0 #m0 #_ #T #HTU #Hl0i #Hilm0
  elim (lift_split … HTU i m0) -HTU /2 width=2 by/
| #I #L #K0 #U #W #l #i #j #Hli #Hij #HnU #HLK0 #_ #IHW #K #s #l0 #m0 #HLK #T #HTU #Hl0i #Hilm0
  elim (ylt_split j l0) #H1
  [ elim (drop_conf_lt … HLK … HLK0) -L // #L0 #V #H #HKL0 #HVW
    @(IHW … HKL0 … HVW)
    [ /3 width=1 by monotonic_yle_minus_dx, yle_pred/
    | >yplus_pred1 /2 width=1 by ylt_to_minus/
      <yplus_minus_comm_inj /3 width=1 by monotonic_yle_minus_dx, yle_pred, ylt_fwd_le/
    ]
  | elim (lift_split … HTU j m0) -HTU /3 width=3 by ylt_yle_trans, ylt_fwd_le/
  ]
]
qed-.

lemma frees_inv_lift_ge: ∀L,U,l,i. L ⊢ i ϵ 𝐅*[l]⦃U⦄ →
                         ∀K,s,l0,m0. ⬇[s, l0, m0] L ≡ K →
                         ∀T. ⬆[l0, m0] T ≡ U → l0 + m0 ≤ i →
                         K ⊢ i-m0 ϵ𝐅*[l-yinj m0]⦃T⦄.
#L #U #l #i #H elim H -L -U -l -i
[ #L #U #l #i #HnU #K #s #l0 #m0 #HLK #T #HTU #Hlm0i -L -s
  elim (yle_inv_plus_inj2 … Hlm0i) -Hlm0i #Hl0im0 #Hm0i @frees_eq #X #HXT -K
  elim (lift_trans_le … HXT … HTU) -T // >ymax_pre_sn /2 width=2 by/
| #I #L #K0 #U #W #l #i #j #Hli #Hij #HnU #HLK0 #_ #IHW #K #s #l0 #m0 #HLK #T #HTU #Hlm0i
  elim (ylt_split j l0) #H1
  [ elim (drop_conf_lt … HLK … HLK0) -L // #L0 #V #H #HKL0 #HVW
    elim (yle_inv_plus_inj2 … Hlm0i) #H0 #Hm0i
    @(frees_be … H) -H
    [ /3 width=1 by yle_plus_dx1_trans, monotonic_yle_minus_dx/
    | /2 width=3 by ylt_yle_trans/
    | #X #HXT elim (lift_trans_ge … HXT … HTU) -T /2 width=2 by ylt_fwd_le_succ1/
    | lapply (IHW … HKL0 … HVW ?) // -I -K -K0 -L0 -V -W -T -U -s
      >yplus_pred1 /2 width=1 by ylt_to_minus/
      <yplus_minus_comm_inj /3 width=1 by monotonic_yle_minus_dx, yle_pred, ylt_fwd_le/
    ]
  | elim (ylt_split j (l0+m0)) #H2
    [ -L -I -W elim (yle_inv_inj2 … H1) -H1 #x #H1 #H destruct
      lapply (ylt_plus2_to_minus_inj1 … H2) /2 width=1 by yle_inj/ #H3
      lapply (ylt_fwd_lt_O1 … H3) -H3 #H3
      elim (lift_split … HTU j (m0-1)) -HTU /2 width=1 by yle_inj/
      [ >minus_minus_associative /2 width=1 by ylt_inv_inj/ <minus_n_n
        -H2 #X #_ #H elim (HnU … H)
      | <yminus_inj >yminus_SO2 >yplus_pred2 /2 width=1 by ylt_fwd_le_pred2/
      ]
    | lapply (drop_conf_ge … HLK … HLK0 ?) // -L #HK0
      elim ( yle_inv_plus_inj2 … H2) -H2 #H2 #Hm0j
      @(frees_be … HK0)
      [ /2 width=1 by monotonic_yle_minus_dx/
      | /2 width=1 by monotonic_ylt_minus_dx/
      | #X #HXT elim (lift_trans_le … HXT … HTU) -T //
        <yminus_inj >ymax_pre_sn /2 width=2 by/
      | <yminus_inj >yplus_minus_assoc_comm_inj //
        >ymax_pre_sn /3 width=5 by yle_trans, ylt_fwd_le/
      ]
    ]
  ]
]
qed-.
