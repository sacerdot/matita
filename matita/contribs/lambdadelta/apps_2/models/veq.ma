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

include "apps_2/models/model_props.ma".

(* EVALUATION EQUIVALENCE ***************************************************)

definition veq (M): relation (evaluation M) ≝
                    λv1,v2. ∀d. v1 d ≗ v2 d.

interpretation "evaluation equivalence (model)"
   'RingEq M v1 v2 = (veq M v1 v2).

(* Basic properties *********************************************************)

lemma veq_refl (M): is_model M →
                    reflexive … (veq M).
/2 width=1 by mr/ qed.

lemma veq_repl (M): is_model M →
                    replace_2 … (veq M) (veq M) (veq M).
/2 width=5 by mq/ qed-.

lemma veq_sym (M): is_model M → symmetric … (veq M).
/3 width=5 by veq_repl, veq_refl/ qed-.

lemma veq_trans (M): is_model M → Transitive … (veq M).
/3 width=5 by veq_repl, veq_refl/ qed-.

lemma veq_canc_sn (M): is_model M → left_cancellable … (veq M).
/3 width=3 by veq_trans, veq_sym/ qed-.

lemma veq_canc_dx (M): is_model M → right_cancellable … (veq M).
/3 width=3 by veq_trans, veq_sym/ qed-.

(* Properties with evaluation lift ******************************************)

theorem vlift_swap (M): is_model M →
                        ∀i1,i2. i1 ≤ i2 →
                        ∀lv,d1,d2. ⫯[i1←d1] ⫯[i2←d2] lv ≗{M} ⫯[↑i2←d2] ⫯[i1←d1] lv.
#M #HM #i1 #i2 #Hi12 #lv #d1 #d2 #j
elim (lt_or_eq_or_gt j i1) #Hji1 destruct
[ lapply (lt_to_le_to_lt … Hji1 Hi12) #Hji2
  >vlift_lt // >vlift_lt // >vlift_lt /2 width=1 by lt_S/ >vlift_lt //
  /2 width=1 by veq_refl/
| >vlift_eq >vlift_lt /2 width=1 by monotonic_le_plus_l/ >vlift_eq
  /2 width=1 by mr/
| >vlift_gt // elim (lt_or_eq_or_gt (↓j) i2) #Hji2 destruct
  [ >vlift_lt // >vlift_lt /2 width=1 by lt_minus_to_plus/ >vlift_gt //
    /2 width=1 by veq_refl/
  | >vlift_eq <(lt_succ_pred … Hji1) >vlift_eq
    /2 width=1 by mr/
  | lapply (le_to_lt_to_lt … Hi12 Hji2) #Hi1j
    >vlift_gt // >vlift_gt /2 width=1 by lt_minus_to_plus_r/ >vlift_gt //
    /2 width=1 by veq_refl/
  ]
]
qed.

lemma vlift_comp (M): is_model M →
                      ∀i. compatible_3 … (vlift M i) (sq M) (veq M) (veq M).
#M #HM #i #d1 #d2 #Hd12 #lv1 #lv2 #HLv12 #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >vlift_lt // >vlift_lt //
| >vlift_eq >vlift_eq //
| >vlift_gt // >vlift_gt //
]
qed-.

(* Properies with term interpretation ***************************************) 

lemma ti_comp (M): is_model M →
                   ∀T,gv1,gv2. gv1 ≗ gv2 → ∀lv1,lv2. lv1 ≗ lv2 →
                   ⟦T⟧[gv1, lv1] ≗{M} ⟦T⟧[gv2, lv2].
#M #HM #T elim T -T * [||| #p * | * ]
[ /4 width=5 by seq_trans, seq_sym, ms/
| /4 width=5 by seq_sym, ml, mq/
| /4 width=3 by seq_trans, seq_sym, mg/
| /5 width=5 by vlift_comp, seq_sym, md, mq/
| /5 width=1 by vlift_comp, mi, mr/
| /4 width=5 by seq_sym, ma, mp, mq/
| /4 width=5 by seq_sym, me, mq/
]
qed.
