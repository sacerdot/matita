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

lemma cpy_fwd_nlift2_ge: ∀G,L,U1,U2,l,m. ⦃G, L⦄ ⊢ U1 ▶[l, m] U2 →
                         ∀i. l ≤ i → (∀T2. ⬆[i, 1] T2 ≡ U2 → ⊥) →
                         (∀T1. ⬆[i, 1] T1 ≡ U1 → ⊥) ∨
                         ∃∃I,K,W,j. l ≤ yinj j & j < i & ⬇[j]L ≡ K.ⓑ{I}W &
                                    (∀V. ⬆[⫰(i-j), 1] V ≡ W → ⊥) & (∀T1. ⬆[j, 1] T1 ≡ U1 → ⊥).
#G #L #U1 #U2 #l #m #H elim H -G -L -U1 -U2 -l -m
[ /3 width=2 by or_introl/
| #I #G #L #K #V #W #j #l #m #Hlj #Hjlm #HLK #HVW #i #Hli #HnW
  elim (ylt_split j i) #Hij
  [ @or_intror @(ex5_4_intro … HLK) // -HLK
    [ #X #HXV elim (lift_trans_le … HXV … HVW ?) -V // #Y #HXY
      <yminus_succ2 <yplus_inj >yplus_SO2 >ymax_pre_sn /2 width=2 by ylt_fwd_le_succ1/
    | -HnW /3 width=7 by lift_inv_lref2_be, ylt_inj/
    ]
  | elim (lift_split … HVW i j) -HVW //
    #X #_ #H elim HnW -HnW //
  ]
| #a #I #G #L #W1 #W2 #U1 #U2 #l #m #_ #_ #IHW12 #IHU12 #i #Hli #H elim (nlift_inv_bind … H) -H
  [ #HnW2 elim (IHW12 … HnW2) -IHW12 -HnW2 -IHU12 //
    [ /4 width=9 by nlift_bind_sn, or_introl/
    | * /5 width=9 by nlift_bind_sn, ex5_4_intro, or_intror/
    ]
  | #HnU2 elim (IHU12 … HnU2) -IHU12 -HnU2 -IHW12 /2 width=1 by yle_succ/
    [ /4 width=9 by nlift_bind_dx, or_introl/
    | * #J #K #W #j #Hlj elim (yle_inv_succ1 … Hlj) -Hlj #Hlj #Hj
      <Hj >yminus_succ #Hji #HLK #HnW
      lapply (drop_inv_drop1_lt … HLK ?) /2 width=1 by ylt_O/ -HLK #HLK
      <yminus_SO2 in Hlj; #Hlj #H4
      @or_intror @(ex5_4_intro … HLK) (**) (* explicit constructors *)
      /3 width=9 by nlift_bind_dx, ylt_pred, ylt_inj/
    ]
  ]
| #I #G #L #W1 #W2 #U1 #U2 #l #m #_ #_ #IHW12 #IHU12 #i #Hli #H elim (nlift_inv_flat … H) -H
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
