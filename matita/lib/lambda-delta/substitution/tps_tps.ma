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

lemma tps_trans: ∀L,T1,T,d,e. L ⊢ T1 [d, e] ≫ T → ∀T2. L ⊢ T [d, e] ≫ T2 →
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

axiom tps_conf: ∀L,T0,d,e,T1. L ⊢ T0 [d, e] ≫ T1 → ∀T2. L ⊢ T0 [d, e] ≫ T2 →
                  ∃∃T. L ⊢ T1 [d, e] ≫ T & L ⊢ T2 [d, e] ≫ T.

(*
      Theorem subst0_subst0: (t1,t2,u2:?; j:?) (subst0 j u2 t1 t2) ->
                             (u1,u:?; i:?) (subst0 i u u1 u2) ->
                             (EX t | (subst0 j u1 t1 t) & (subst0 (S (plus i j)) u t t2)).

      Theorem subst0_subst0_back: (t1,t2,u2:?; j:?) (subst0 j u2 t1 t2) ->
                                  (u1,u:?; i:?) (subst0 i u u2 u1) ->
                                  (EX t | (subst0 j u1 t1 t) & (subst0 (S (plus i j)) u t2 t)).

*)
