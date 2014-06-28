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

include "basic_2/multiple/frees_lift.ma".
include "basic_2/multiple/llor_alt.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

(* Advanced properties ******************************************************)

lemma llor_skip: ∀L1,L2,U,d. |L1| = |L2| → yinj (|L1|) ≤ d → L1 ⩖[U, d] L2 ≡ L1.
#L1 #L2 #U #d #HL12 #Hd @and3_intro // -HL12
#I1 #I2 #I #K1 #K2 #K #W1 #W2 #W #i #HLK1 #_ #HLK -L2 -K2
lapply (drop_mono … HLK … HLK1) -HLK #H destruct
lapply (drop_fwd_length_lt2 … HLK1) -K1
/5 width=3 by ylt_yle_trans, ylt_inj, or3_intro0, and3_intro/
qed.

(* Note: lemma 1400 concludes the "big tree" theorem *)
lemma llor_total: ∀L1,L2,T,d. |L1| = |L2| → ∃L. L1 ⩖[T, d] L2 ≡ L.
#L1 @(lenv_ind_alt … L1) -L1
[ #L2 #T #d #H >(length_inv_zero_sn … H) -L2 /2 width=2 by ex_intro/
| #I1 #L1 #V1 #IHL1 #Y #T #d >ltail_length #H
  elim (length_inv_pos_sn_ltail … H) -H #I2 #L2 #V2 #HL12 #H destruct
  elim (ylt_split d (|ⓑ{I1}V1.L1|))
  [ elim (frees_dec (ⓑ{I1}V1.L1) T d (|L1|)) #HnU
    elim (IHL1 L2 T d) // -IHL1 -HL12
    [ #L #HL12 >ltail_length /4 width=2 by llor_tail_frees, ylt_fwd_succ2, ex_intro/ 
    | /4 width=2 by llor_tail_cofrees, ex_intro/
    ]
  | -IHL1 /4 width=3 by llor_skip, plus_to_minus, ex_intro/
  ]
]
qed-.
