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
include "basic_2/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

lemma frees_dec: ∀L,U,d,i. Decidable (frees d L U i).
#L #U @(f2_ind … rfw … L U) -L -U
#n #IH #L * *
[ -IH /3 width=5 by frees_inv_sort, or_intror/
| #j #Hn #d #i elim (lt_or_eq_or_gt i j) #Hji
  [ -n @or_intror #H elim (lt_refl_false i)
    lapply (frees_inv_lref_ge … H ?) -L -d /2 width=1 by lt_to_le/
  | -n /2 width=1 by or_introl/
  | elim (ylt_split j d) #Hdi
    [ -n @or_intror #H elim (lt_refl_false i)
      lapply (frees_inv_lref_skip … H ?) -L //
    | elim (lt_or_ge j (|L|)) #Hj
      [ elim (drop_O1_lt (Ⓕ) L j) // -Hj #I #K #W #HLK destruct
        elim (IH K W … 0 (i-j-1)) -IH [1,3: /3 width=5 by frees_lref_be, drop_fwd_rfw, or_introl/ ] #HnW
        @or_intror #H elim (frees_inv_lref_lt … H) // #Z #Y #X #_ #HLY -d
        lapply (drop_mono … HLY … HLK) -L #H destruct /2 width=1 by/  
      | -n @or_intror #H elim (lt_refl_false i)
        lapply (frees_inv_lref_free … H ?) -d //
      ]
    ]
  ]
| -IH /3 width=5 by frees_inv_gref, or_intror/
| #a #I #W #U #Hn #d #i destruct
  elim (IH L W … d i) [1,3: /3 width=1 by frees_bind_sn, or_introl/ ] #HnW
  elim (IH (L.ⓑ{I}W) U … (⫯d) (i+1)) -IH [1,3: /3 width=1 by frees_bind_dx, or_introl/ ] #HnU
  @or_intror #H elim (frees_inv_bind … H) -H /2 width=1 by/
| #I #W #U #Hn #d #i destruct
  elim (IH L W … d i) [1,3: /3 width=1 by frees_flat_sn, or_introl/ ] #HnW
  elim (IH L U … d i) -IH [1,3: /3 width=1 by frees_flat_dx, or_introl/ ] #HnU
  @or_intror #H elim (frees_inv_flat … H) -H /2 width=1 by/
]
qed-.

lemma frees_S: ∀L,U,d,i. L ⊢ i ϵ 𝐅*[yinj d]⦃U⦄ → ∀I,K,W. ⇩[d] L ≡ K.ⓑ{I}W →
               (K ⊢ i-d-1 ϵ 𝐅*[0]⦃W⦄ → ⊥) → L ⊢ i ϵ 𝐅*[⫯d]⦃U⦄.
#L #U #d #i #H elim (frees_inv … H) -H /3 width=2 by frees_eq/
* #I #K #W #j #Hdj #Hji #HnU #HLK #HW #I0 #K0 #W0 #HLK0 #HnW0
lapply (yle_inv_inj … Hdj) -Hdj #Hdj
elim (le_to_or_lt_eq … Hdj) -Hdj
[ -I0 -K0 -W0 /3 width=9 by frees_be, yle_inj/
| -Hji -HnU #H destruct
  lapply (drop_mono … HLK0 … HLK) #H destruct -I
  elim HnW0 -L -U -HnW0 //
]
qed.

(* Note: lemma 1250 *)
lemma frees_bind_dx_O: ∀a,I,L,W,U,i. L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[0]⦃U⦄ →
                       L ⊢ i ϵ 𝐅*[0]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #i #HU elim (frees_dec L W 0 i)
/4 width=5 by frees_S, frees_bind_dx, frees_bind_sn/
qed.

(* Properties on relocation *************************************************)

lemma frees_lift_ge: ∀K,T,d,i. K ⊢ i ϵ𝐅*[d]⦃T⦄ →
                     ∀L,s,d0,e0. ⇩[s, d0, e0] L ≡ K →
                     ∀U. ⇧[d0, e0] T ≡ U → d0 ≤ i →
                     L ⊢ i+e0 ϵ 𝐅*[d]⦃U⦄.
#K #T #d #i #H elim H -K -T -d -i
[ #K #T #d #i #HnT #L #s #d0 #e0 #_ #U #HTU #Hd0i -K -s
  @frees_eq #X #HXU elim (lift_div_le … HTU … HXU) -U /2 width=2 by/
| #I #K #K0 #T #V #d #i #j #Hdj #Hji #HnT #HK0 #HV #IHV #L #s #d0 #e0 #HLK #U #HTU #Hd0i
  elim (lt_or_ge j d0) #H1
  [ elim (drop_trans_lt … HLK … HK0) // -K #L0 #W #HL0 #HLK0 #HVW
    @(frees_be … HL0) -HL0 -HV
    /3 width=3 by lt_plus_to_minus_r, lt_to_le_to_lt/
    [ #X #HXU >(plus_minus_m_m d0 1) in HTU; /2 width=2 by ltn_to_ltO/ #HTU
      elim (lift_div_le … HXU … HTU ?) -U /2 width=2 by monotonic_pred/
    | >minus_plus <plus_minus // <minus_plus
      /3 width=5 by monotonic_le_minus_l2/
    ]
  | lapply (drop_trans_ge … HLK … HK0 ?) // -K #HLK0
    lapply (drop_inv_gen … HLK0) >commutative_plus -HLK0 #HLK0
    @(frees_be … HLK0) -HLK0 -IHV
    /2 width=1 by yle_plus_dx1_trans, lt_minus_to_plus/
    #X #HXU elim (lift_div_le … HTU … HXU) -U /2 width=2 by/
  ]
]
qed.

(* Inversion lemmas on relocation *******************************************)

lemma frees_inv_lift_be: ∀L,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                         ∀K,s,d0,e0. ⇩[s, d0, e0+1] L ≡ K →
                         ∀T. ⇧[d0, e0+1] T ≡ U → d0 ≤ i → i ≤ d0 + e0 → ⊥.
#L #U #d #i #H elim H -L -U -d -i
[ #L #U #d #i #HnU #K #s #d0 #e0 #_ #T #HTU #Hd0i #Hide0
  elim (lift_split … HTU i e0) -HTU /2 width=2 by/
| #I #L #K0 #U #W #d #i #j #Hdi #Hij #HnU #HLK0 #_ #IHW #K #s #d0 #e0 #HLK #T #HTU #Hd0i #Hide0
  elim (lt_or_ge j d0) #H1
  [ elim (drop_conf_lt … HLK … HLK0) -L // #L0 #V #H #HKL0 #HVW
    @(IHW … HKL0 … HVW)
    [ /2 width=1 by monotonic_le_minus_l2/
    | >minus_plus >minus_plus >plus_minus /2 width=1 by monotonic_le_minus_l/
    ]
  | elim (lift_split … HTU j e0) -HTU /3 width=3 by lt_to_le_to_lt, lt_to_le/
  ]
]
qed-.

lemma frees_inv_lift_ge: ∀L,U,d,i. L ⊢ i ϵ 𝐅*[d]⦃U⦄ →
                         ∀K,s,d0,e0. ⇩[s, d0, e0] L ≡ K →
                         ∀T. ⇧[d0, e0] T ≡ U → d0 + e0 ≤ i →
                         K ⊢ i-e0 ϵ𝐅*[d-yinj e0]⦃T⦄.
#L #U #d #i #H elim H -L -U -d -i
[ #L #U #d #i #HnU #K #s #d0 #e0 #HLK #T #HTU #Hde0i -L -s
  elim (le_inv_plus_l … Hde0i) -Hde0i #Hd0ie0 #He0i @frees_eq #X #HXT -K
  elim (lift_trans_le … HXT … HTU) -T // <plus_minus_m_m /2 width=2 by/
| #I #L #K0 #U #W #d #i #j #Hdi #Hij #HnU #HLK0 #_ #IHW #K #s #d0 #e0 #HLK #T #HTU #Hde0i
  elim (lt_or_ge j d0) #H1
  [ elim (drop_conf_lt … HLK … HLK0) -L // #L0 #V #H #HKL0 #HVW
    elim (le_inv_plus_l … Hde0i) #H0 #He0i
    @(frees_be … H) -H
    [ /3 width=1 by yle_plus_dx1_trans, monotonic_yle_minus_dx/
    | /2 width=3 by lt_to_le_to_lt/
    | #X #HXT elim (lift_trans_ge … HXT … HTU) -T /2 width=2 by/
    | lapply (IHW … HKL0 … HVW ?) // -I -K -K0 -L0 -V -W -T -U -s
      >minus_plus >minus_plus >plus_minus /2 width=1 by monotonic_le_minus_l/
    ]
  | elim (lt_or_ge j (d0+e0)) [ >commutative_plus |] #H2
    [ -L -I -W lapply (lt_plus_to_minus ???? H2) // -H2 #H2
      elim (lift_split … HTU j (e0-1)) -HTU //
      [ >minus_minus_associative /2 width=2 by ltn_to_ltO/ <minus_n_n
        #X #_ #H elim (HnU … H)
      | >commutative_plus /3 width=1 by le_minus_to_plus, monotonic_pred/
      ]
    | lapply (drop_conf_ge … HLK … HLK0 ?) // -L #HK0
      elim (le_inv_plus_l … H2) -H2 #H2 #He0j
      @(frees_be … HK0)
      [ /2 width=1 by monotonic_yle_minus_dx/
      | /2 width=1 by monotonic_lt_minus_l/
      | #X #HXT elim (lift_trans_le … HXT … HTU) -T // <plus_minus_m_m /2 width=2 by/
      | >arith_b1 /2 width=5 by/
      ]
    ]
  ]
]
qed-.
