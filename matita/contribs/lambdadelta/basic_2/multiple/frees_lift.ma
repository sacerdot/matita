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

include "basic_2/substitution/ldrop_ldrop.ma".
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
      [ elim (ldrop_O1_lt (Ⓕ) L j) // -Hj #I #K #W #HLK destruct
        elim (IH K W … 0 (i-j-1)) -IH [1,3: /3 width=5 by frees_lref_be, ldrop_fwd_rfw, or_introl/ ] #HnW
        @or_intror #H elim (frees_inv_lref_lt … H) // #Z #Y #X #_ #HLY -d
        lapply (ldrop_mono … HLY … HLK) -L #H destruct /2 width=1 by/  
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
  lapply (ldrop_mono … HLK0 … HLK) #H destruct -I
  elim HnW0 -L -U -HnW0 //
]
qed.

(* Note: lemma 1250 *)
lemma frees_bind_dx_O: ∀a,I,L,W,U,i. L.ⓑ{I}W ⊢ i+1 ϵ 𝐅*[0]⦃U⦄ →
                       L ⊢ i ϵ 𝐅*[0]⦃ⓑ{a,I}W.U⦄.
#a #I #L #W #U #i #HU elim (frees_dec L W 0 i)
/4 width=5 by frees_S, frees_bind_dx, frees_bind_sn/
qed.
