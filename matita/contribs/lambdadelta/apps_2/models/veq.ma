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

(* EVALUATION EQUIVALENCE  **************************************************)

definition veq (M): relation (evaluation M) ≝
                    λv1,v2. ∀d. v1 d ≗ v2 d.

interpretation "evaluation equivalence (model)"
   'RingEq M v1 v2 = (veq M v1 v2).

(* Basic properties *********************************************************)

lemma veq_refl (M): is_model M →
                    reflexive … (veq M).
/2 width=1 by mq/ qed.

lemma veq_repl (M): is_model M →
                    replace_2 … (veq M) (veq M) (veq M).
/2 width=5 by mr/ qed-.

lemma veq_sym (M): is_model M → symmetric … (veq M).
/3 width=5 by veq_repl, veq_refl/ qed-.

lemma veq_trans (M): is_model M → Transitive … (veq M).
/3 width=5 by veq_repl, veq_refl/ qed-.

(* Properties with extebsional equivalence **********************************)

lemma ext_veq (M): is_model M →
                   ∀lv1,lv2. lv1 ≐ lv2 → lv1 ≗{M} lv2.
/2 width=1 by mq/ qed.

lemma veq_repl_exteq (M): is_model M →
                          replace_2 … (veq M) (exteq …) (exteq …).
/2 width=5 by mr/ qed-.

lemma exteq_veq_trans (M): ∀lv1,lv. lv1 ≐ lv →
                           ∀lv2. lv ≗{M} lv2 → lv1 ≗ lv2.
// qed-.

(* Properties with evaluation evaluation lift *******************************)

theorem vlift_swap (M): ∀i1,i2. i1 ≤ i2 →
                        ∀lv,d1,d2. ⫯[i1←d1] ⫯[i2←d2] lv ≐{?,dd M} ⫯[↑i2←d2] ⫯[i1←d1] lv.
#M #i1 #i2 #Hi12 #lv #d1 #d2 #j
elim (lt_or_eq_or_gt j i1) #Hji1 destruct
[ >vlift_lt // >vlift_lt /2 width=3 by lt_to_le_to_lt/
  >vlift_lt /3 width=3 by lt_S, lt_to_le_to_lt/ >vlift_lt //
| >vlift_eq >vlift_lt /2 width=1 by monotonic_le_plus_l/ >vlift_eq //
| >vlift_gt // elim (lt_or_eq_or_gt (↓j) i2) #Hji2 destruct
  [ >vlift_lt // >vlift_lt /2 width=1 by lt_minus_to_plus/ >vlift_gt //
  | >vlift_eq <(lt_succ_pred … Hji1) >vlift_eq //
  | >vlift_gt // >vlift_gt /2 width=1 by lt_minus_to_plus_r/ >vlift_gt /2 width=3 by le_to_lt_to_lt/
  ]
]
qed-.

lemma vlift_comp (M): ∀i. compatible_3 … (vlift M i) (sq M) (veq M) (veq M).
#m #i #d1 #d2 #Hd12 #lv1 #lv2 #HLv12 #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >vlift_lt // >vlift_lt //
| >vlift_eq >vlift_eq //
| >vlift_gt // >vlift_gt //
]
qed-.

(* Properies with term interpretation ***************************************) 

lemma ti_comp_l (M): is_model M →
                     ∀T,gv,lv1,lv2. lv1 ≗{M} lv2 →
                     ⟦T⟧[gv, lv1] ≗ ⟦T⟧[gv, lv2].
#M #HM #T elim T -T * [||| #p * | * ]
[ /4 width=3 by seq_trans, seq_sym, ms/
| /4 width=5 by seq_sym, ml, mr/
| /4 width=3 by seq_trans, seq_sym, mg/
| /5 width=5 by vlift_comp, seq_sym, md, mr/
| /5 width=1 by vlift_comp, mi, mq/
| /4 width=5 by seq_sym, ma, mc, mr/
| /4 width=5 by seq_sym, me, mr/
]
qed.

lemma ti_ext_l (M): is_model M →
                    ∀T,gv,lv1,lv2. lv1 ≐ lv2 →
                    ⟦T⟧[gv, lv1] ≗{M} ⟦T⟧[gv, lv2].
/3 width=1 by ti_comp_l, ext_veq/ qed.
