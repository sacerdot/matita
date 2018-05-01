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

(* Properties with evaluation push ******************************************)

lemma push_comp (M): ∀i. compatible_3 … (push M i) (sq M) (veq M) (veq M).
#m #i #d1 #d2 #Hd12 #lv1 #lv2 #HLv12 #j
elim (lt_or_eq_or_gt j i) #Hij destruct
[ >(push_lt … Hij) >(push_lt … Hij) //
| >(push_eq …) >(push_eq …) //
| >(push_gt … Hij) >(push_gt … Hij) //
]
qed.

(* Inversion lemmas with evaluation push *************************************)

axiom veq_inv_push_sn: ∀M,lv1,y2,d1,i. ⫯[i←d1]lv1 ≗{M} y2 →
                       ∃∃lv2,d2. lv1 ≗ lv2 & d1 ≗ d2 & ⫯[i←d2]lv2 = y2.   
(*
#M #lv1 #y2 #d1 #i #H 
*)
(* Properies with term interpretation ***************************************) 

lemma ti_comp_l (M): is_model M →
                     ∀T,gv,lv1,lv2. lv1 ≗{M} lv2 →
                     ⟦T⟧[gv, lv1] ≗ ⟦T⟧[gv, lv2].
#M #HM #T elim T -T * [||| #p * | * ]
[ /4 width=3 by seq_trans, seq_sym, ms/
| /4 width=5 by seq_sym, ml, mr/
| /4 width=3 by seq_trans, seq_sym, mg/
| /5 width=5 by push_comp, seq_sym, md, mr/
| /5 width=1 by push_comp, mi, mq/
| /4 width=5 by seq_sym, ma, mc, mr/
| /4 width=5 by seq_sym, me, mr/
]
qed.
