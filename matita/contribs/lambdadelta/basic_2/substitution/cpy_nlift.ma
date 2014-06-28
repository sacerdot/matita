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

include "basic_2/substitution/lift_neg.ma".
include "basic_2/substitution/lift_lift.ma".
include "basic_2/substitution/cpy.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* Inversion lemmas on negated relocation ***********************************)

lemma cpy_fwd_nlift2_ge: ∀G,L,U1,U2,d,e. ⦃G, L⦄ ⊢ U1 ▶[d, e] U2 →
                         ∀i. d ≤ yinj i → (∀T2. ⇧[i, 1] T2 ≡ U2 → ⊥) →
                         (∀T1. ⇧[i, 1] T1 ≡ U1 → ⊥) ∨
                         ∃∃I,K,W,j. d ≤ yinj j & j < i & ⇩[j]L ≡ K.ⓑ{I}W &
                                    (∀V. ⇧[i-j-1, 1] V ≡ W → ⊥) & (∀T1. ⇧[j, 1] T1 ≡ U1 → ⊥).
#G #L #U1 #U2 #d #e #H elim H -G -L -U1 -U2 -d -e
[ /3 width=2 by or_introl/
| #I #G #L #K #V #W #j #d #e #Hdj #Hjde #HLK #HVW #i #Hdi #HnW
  elim (lt_or_ge j i) #Hij
  [ @or_intror @(ex5_4_intro … HLK) // -HLK
    [ #X #HXV elim (lift_trans_le … HXV … HVW ?) -V //
      #Y #HXY >minus_plus <plus_minus_m_m /2 width=2 by/
    | -HnW /2 width=7 by lift_inv_lref2_be/
    ]
  | elim (lift_split … HVW i j) -HVW //
    #X #_ #H elim HnW -HnW //
  ]
| #a #I #G #L #W1 #W2 #U1 #U2 #d #e #_ #_ #IHW12 #IHU12 #i #Hdi #H elim (nlift_inv_bind … H) -H
  [ #HnW2 elim (IHW12 … HnW2) -IHW12 -HnW2 -IHU12 //
    [ /4 width=9 by nlift_bind_sn, or_introl/
    | * /5 width=9 by nlift_bind_sn, ex5_4_intro, or_intror/
    ]
  | #HnU2 elim (IHU12 … HnU2) -IHU12 -HnU2 -IHW12 /2 width=1 by yle_succ/
    [ /4 width=9 by nlift_bind_dx, or_introl/
    | * #J #K #W #j #Hdj #Hji #HLK #HnW
      elim (yle_inv_succ1 … Hdj) -Hdj #Hdj #Hj
      lapply (ylt_O … Hj) -Hj #Hj
      lapply (drop_inv_drop1_lt … HLK ?) // -HLK #HLK
      >(plus_minus_m_m j 1) in ⊢ (%→?); [2: /3 width=3 by yle_trans, yle_inv_inj/ ]
      #HnU1 <minus_le_minus_minus_comm in HnW;
      /5 width=9 by nlift_bind_dx, monotonic_lt_pred, lt_plus_to_minus_r, ex5_4_intro, or_intror/
    ]
  ]
| #I #G #L #W1 #W2 #U1 #U2 #d #e #_ #_ #IHW12 #IHU12 #i #Hdi #H elim (nlift_inv_flat … H) -H
  [ #HnW2 elim (IHW12 … HnW2) -IHW12 -HnW2 -IHU12 //
    [ /4 width=9 by nlift_flat_sn, or_introl/
    | * /5 width=9 by nlift_flat_sn, ex5_4_intro, or_intror/
    ]
  | #HnU2 elim (IHU12 … HnU2) -IHU12 -HnU2 -IHW12 //
    [ /4 width=9 by nlift_flat_dx, or_introl/
    | * /5 width=9 by nlift_flat_dx, ex5_4_intro, or_intror/
  ]
]
qed-.
