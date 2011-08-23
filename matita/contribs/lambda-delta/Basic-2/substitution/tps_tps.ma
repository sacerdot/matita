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

include "Basic-2/substitution/tps_lift.ma".

(* PARALLEL SUBSTITUTION ON TERMS *******************************************)

(* Main properties **********************************************************)

theorem tps_conf: ∀L,T0,T1,d,e. L ⊢ T0 [d, e] ≫ T1 → ∀T2. L ⊢ T0 [d, e] ≫ T2 →
                  ∃∃T. L ⊢ T1 [d, e] ≫ T & L ⊢ T2 [d, e] ≫ T.
#L #T0 #T1 #d #e #H elim H -H L T0 T1 d e
[ /2/
| /2/
| #L #K1 #V1 #T1 #i1 #d #e #Hdi1 #Hi1de #HLK1 #HVT1 #T2 #H
  elim (tps_inv_lref1 … H) -H
  [ #HX destruct -T2 /4/
  | * #K2 #V2 #_ #_ #HLK2 #HVT2
    lapply (drop_mono … HLK1 … HLK2) -HLK1 #H destruct -V1 K1
    >(lift_mono … HVT1 … HVT2) -HVT1 /2/
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

theorem tps_trans_down: ∀L,T1,T0,d1,e1. L ⊢ T1 [d1, e1] ≫ T0 →
                        ∀T2,d2,e2. L ⊢ T0 [d2, e2] ≫ T2 → d2 + e2 ≤ d1 →
                        ∃∃T. L ⊢ T1 [d2, e2] ≫ T & L ⊢ T [d1, e1] ≫ T2.
#L #T1 #T0 #d1 #e1 #H elim H -L T1 T0 d1 e1
[ /2/
| /2/
| #L #K #V #W #i1 #d1 #e1 #Hdi1 #Hide1 #HLK #HVW #T2 #d2 #e2 #HWT2 #Hde2d1
  lapply (transitive_le … Hde2d1 Hdi1) -Hde2d1 #Hde2i1
  lapply (tps_weak … HWT2 0 (i1 + 1) ? ?) -HWT2; normalize /2/ -Hde2i1 #HWT2
  <(tps_inv_lift1_eq … HWT2 … HVW) -HWT2 /4/
| #L #I #V1 #V0 #T1 #T0 #d1 #e1 #_ #_ #IHV10 #IHT10 #X #d2 #e2 #HX #de2d1
  elim (tps_inv_bind1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct -X;
  lapply (tps_leq_repl … HT02 (L. 𝕓{I} V1) ?) -HT02 /2/ #HT02
  elim (IHV10 … HV02 ?) -IHV10 HV02 // #V
  elim (IHT10 … HT02 ?) -IHT10 HT02 [2: /2/ ] #T #HT1 #HT2
  lapply (tps_leq_repl … HT2 (L. 𝕓{I} V) ?) -HT2 /3 width=6/
| #L #I #V1 #V0 #T1 #T0 #d1 #e1 #_ #_ #IHV10 #IHT10 #X #d2 #e2 #HX #de2d1
  elim (tps_inv_flat1 … HX) -HX #V2 #T2 #HV02 #HT02 #HX destruct -X;
  elim (IHV10 … HV02 ?) -IHV10 HV02 //
  elim (IHT10 … HT02 ?) -IHT10 HT02 // /3 width=6/
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
