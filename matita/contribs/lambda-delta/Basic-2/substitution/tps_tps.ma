(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "lambda-delta/substitution/tps_split.ma".

(* PARTIAL SUBSTITUTION ON TERMS ********************************************)

(* Main properties **********************************************************)
(*
theorem tps_trans: ∀L,T1,T,d,e. L ⊢ T1 [d, e] ≫ T → ∀T2. L ⊢ T [d, e] ≫ T2 →
                   L ⊢ T1 [d, e] ≫ T2.
#L #T1 #T #d #e #H elim H -L T1 T d e
[ //
| //
| #L #K #V #V1 #V2 #i #d #e #Hdi #Hide #HLK #_ #HV12 #IHV12 #T2 #HVT2
  lapply (drop_fwd_drop2 … HLK) #H
  elim (tps_inv_lift1_up … HVT2 … H … HV12 ? ? ?) -HVT2 H HV12 // normalize [2: /2/ ] #V #HV1 #HVT2
  @tps_subst [4,5,6,8: // |1,2,3: skip | /2/ ]
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (tps_inv_bind1 … HX) -HX #V #T #HV2 #HT2 #HX destruct -X;
  @tps_bind /2/ @IHT12 @(tps_leq_repl … HT2) /2/
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (tps_inv_flat1 … HX) -HX #V #T #HV2 #HT2 #HX destruct -X /3/
]
qed.
*)

axiom tps_conf_subst_subst_lt: ∀L,K1,V1,W1,T1,i1,d,e,T2,K2,V2,W2,i2.
   ↓[O, i1] L ≡ K1. 𝕓{Abbr} V1 → ↓[O, i2] L≡ K2. 𝕓{Abbr} V2 →
   K1 ⊢ V1 [O, d + e - i1 - 1] ≫ W1 → K2 ⊢ V2 [O, d + e - i2 - 1] ≫ W2 →
   ↑[O, i1 + 1] W1 ≡ T1 → ↑[O, i2 + 1] W2 ≡ T2 → 
   d ≤ i1 → i1 < d + e → d ≤ i2 → i2 < d + e → i1 < i2 →
   ∃∃T. L ⊢ T1 [d, e] ≫ T & L ⊢ T2 [d, e] ≫ T.  
(*
#L #K1 #V1 #W1 #T1 #i1 #d #e #T2 #K2 #V2 #W2 #i2
#HLK1 #HLK2 #HVW1 #HVW2 #HWT1 #HWT2 #Hdi1 #Hi1de #Hdi2 #Hi2de #Hi12
*)

theorem tps_conf: ∀L,T0,T1,d,e. L ⊢ T0 [d, e] ≫ T1 → ∀T2. L ⊢ T0 [d, e] ≫ T2 →
                  ∃∃T. L ⊢ T1 [d, e] ≫ T & L ⊢ T2 [d, e] ≫ T.
#L #T0 #T1 #d #e #H elim H -H L T0 T1 d e
[ /2/
| /2/
| #L #K1 #V1 #W1 #T1 #i1 #d #e #Hdi1 #Hi1de #HLK1 #HVW1 #HWT1 #IHVW1 #T2 #H
  elim (tps_inv_lref1 … H) -H
  [ -IHVW1 #HX destruct -T2
    @ex2_1_intro [2: // | skip ] /2 width=6/ (**) (* /3 width=9/ is slow *)
  | * #K2 #V2 #W2 #i2 #Hdi2 #Hi2de #HLK2 #HVW2 #HWT2
    elim (lt_or_eq_or_gt i1 i2) #Hi12
    [ @tps_conf_subst_subst_lt /width=19/
    | -HVW1; destruct -i2;
      lapply (transitive_le ? ? (i1 + 1) Hdi2 ?) -Hdi2 // #Hdi2
      lapply (drop_mono … HLK1 … HLK2) -HLK1 Hdi1 Hi1de #H destruct -V1 K1;
      elim (IHVW1 … HVW2) -IHVW1 HVW2 #W #HW1 #HW2
      lapply (drop_fwd_drop2 … HLK2) -HLK2 #HLK2
      elim (lift_total W 0 (i1 + 1)) #T #HWT
      lapply (tps_lift_ge … HW1 … HLK2 HWT1 HWT ?) -HW1 HWT1 //
      lapply (tps_lift_ge … HW2 … HLK2 HWT2 HWT ?) -HW2 HWT2 HLK2 HWT // normalize #HT2 #HT1
      lapply (tps_weak … HT1 d e ? ?) -HT1 [ >arith_i2 // | // ]
      lapply (tps_weak … HT2 d e ? ?) -HT2 [ >arith_i2 // | // ]
      /2/
    | @ex2_1_comm @tps_conf_subst_subst_lt /width=19/
    ]
  ]
| #L #I #V0 #V1 #T0 #T1 #d #e #_ #_ #IHV01 #IHT01 #X #HX
  elim (tps_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct -X; 
  elim (IHV01 … HV02) -IHV01 HV02 #V #HV1 #HV2
  elim (IHT01 … HT02) -IHT01 HT02 #T #HT1 #HT2 
  @ex2_1_intro
  [2: @tps_bind [4: @(tps_leq_repl … HT1) /2/ |2: skip ]
  |1: skip
  |3: @tps_bind [2: @(tps_leq_repl … HT2) /2/ ]
  ] // (**) (* /5/ is too slow *)
| #L #I #V0 #V1 #T0 #T1 #d #e #_ #_ #IHV01 #IHT01 #X #HX
  elim (tps_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct -X; 
  elim (IHV01 … HV02) -IHV01 HV02;
  elim (IHT01 … HT02) -IHT01 HT02 /3 width=5/
]
qed.

(*
      Theorem subst0_subst0: (t1,t2,u2:?; j:?) (subst0 j u2 t1 t2) ->
                             (u1,u:?; i:?) (subst0 i u u1 u2) ->
                             (EX t | (subst0 j u1 t1 t) & (subst0 (S (plus i j)) u t t2)).

      Theorem subst0_subst0_back: (t1,t2,u2:?; j:?) (subst0 j u2 t1 t2) ->
                                  (u1,u:?; i:?) (subst0 i u u2 u1) ->
                                  (EX t | (subst0 j u1 t1 t) & (subst0 (S (plus i j)) u t2 t)).

*)
