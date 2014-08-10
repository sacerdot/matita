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

include "basic_2/notation/relations/rliftstar_3.ma".
include "basic_2/substitution/lift.ma".
include "basic_2/multiple/mr2_plus.ma".

(* GENERIC TERM RELOCATION **************************************************)

inductive lifts: list2 nat nat → relation term ≝
| lifts_nil : ∀T. lifts (⟠) T T
| lifts_cons: ∀T1,T,T2,des,d,e.
              ⇧[d,e] T1 ≡ T → lifts des T T2 → lifts ({d, e} @ des) T1 T2
.

interpretation "generic relocation (term)"
   'RLiftStar des T1 T2 = (lifts des T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lifts_inv_nil_aux: ∀T1,T2,des. ⇧*[des] T1 ≡ T2 → des = ⟠ → T1 = T2.
#T1 #T2 #des * -T1 -T2 -des //
#T1 #T #T2 #d #e #des #_ #_ #H destruct
qed-.

lemma lifts_inv_nil: ∀T1,T2. ⇧*[⟠] T1 ≡ T2 → T1 = T2.
/2 width=3 by lifts_inv_nil_aux/ qed-.

fact lifts_inv_cons_aux: ∀T1,T2,des. ⇧*[des] T1 ≡ T2 →
                         ∀d,e,tl. des = {d, e} @ tl →
                         ∃∃T. ⇧[d, e] T1 ≡ T & ⇧*[tl] T ≡ T2.
#T1 #T2 #des * -T1 -T2 -des
[ #T #d #e #tl #H destruct
| #T1 #T #T2 #des #d #e #HT1 #HT2 #hd #he #tl #H destruct
  /2 width=3 by ex2_intro/
qed-.

lemma lifts_inv_cons: ∀T1,T2,d,e,des. ⇧*[{d, e} @ des] T1 ≡ T2 →
                      ∃∃T. ⇧[d, e] T1 ≡ T & ⇧*[des] T ≡ T2.
/2 width=3 by lifts_inv_cons_aux/ qed-.

(* Basic_1: was: lift1_sort *)
lemma lifts_inv_sort1: ∀T2,k,des. ⇧*[des] ⋆k ≡ T2 → T2 = ⋆k.
#T2 #k #des elim des -des
[ #H <(lifts_inv_nil … H) -H //
| #d #e #des #IH #H
  elim (lifts_inv_cons … H) -H #X #H
  >(lift_inv_sort1 … H) -H /2 width=1 by/
]
qed-.

(* Basic_1: was: lift1_lref *)
lemma lifts_inv_lref1: ∀T2,des,i1. ⇧*[des] #i1 ≡ T2 →
                       ∃∃i2. @⦃i1, des⦄ ≡ i2 & T2 = #i2.
#T2 #des elim des -des
[ #i1 #H <(lifts_inv_nil … H) -H /2 width=3 by at_nil, ex2_intro/
| #d #e #des #IH #i1 #H
  elim (lifts_inv_cons … H) -H #X #H1 #H2
  elim (lift_inv_lref1 … H1) -H1 * #Hdi1 #H destruct
  elim (IH … H2) -IH -H2 /3 width=3 by at_lt, at_ge, ex2_intro/
]
qed-.

lemma lifts_inv_gref1: ∀T2,p,des. ⇧*[des] §p ≡ T2 → T2 = §p.
#T2 #p #des elim des -des
[ #H <(lifts_inv_nil … H) -H //
| #d #e #des #IH #H
  elim (lifts_inv_cons … H) -H #X #H
  >(lift_inv_gref1 … H) -H /2 width=1 by/
]
qed-.

(* Basic_1: was: lift1_bind *)
lemma lifts_inv_bind1: ∀a,I,T2,des,V1,U1. ⇧*[des] ⓑ{a,I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⇧*[des] V1 ≡ V2 & ⇧*[des + 1] U1 ≡ U2 &
                                T2 = ⓑ{a,I} V2. U2.
#a #I #T2 #des elim des -des
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #d #e #des #IHdes #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_bind1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHdes … HT2) -IHdes -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

(* Basic_1: was: lift1_flat *)
lemma lifts_inv_flat1: ∀I,T2,des,V1,U1. ⇧*[des] ⓕ{I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⇧*[des] V1 ≡ V2 & ⇧*[des] U1 ≡ U2 &
                                T2 = ⓕ{I} V2. U2.
#I #T2 #des elim des -des
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #d #e #des #IHdes #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_flat1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHdes … HT2) -IHdes -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lifts_simple_dx: ∀T1,T2,des. ⇧*[des] T1 ≡ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 #des #H elim H -T1 -T2 -des /3 width=5 by lift_simple_dx/
qed-.

lemma lifts_simple_sn: ∀T1,T2,des. ⇧*[des] T1 ≡ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
#T1 #T2 #des #H elim H -T1 -T2 -des /3 width=5 by lift_simple_sn/
qed-.

(* Basic properties *********************************************************)

lemma lifts_bind: ∀a,I,T2,V1,V2,des. ⇧*[des] V1 ≡ V2 →
                  ∀T1. ⇧*[des + 1] T1 ≡ T2 →
                  ⇧*[des] ⓑ{a,I} V1. T1 ≡ ⓑ{a,I} V2. T2.
#a #I #T2 #V1 #V2 #des #H elim H -V1 -V2 -des
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #des #d #e #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3 by lift_bind, lifts_cons/
]
qed.

lemma lifts_flat: ∀I,T2,V1,V2,des. ⇧*[des] V1 ≡ V2 →
                  ∀T1. ⇧*[des] T1 ≡ T2 →
                  ⇧*[des] ⓕ{I} V1. T1 ≡ ⓕ{I} V2. T2.
#I #T2 #V1 #V2 #des #H elim H -V1 -V2 -des
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #des #d #e #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3 by lift_flat, lifts_cons/
]
qed.

lemma lifts_total: ∀des,T1. ∃T2. ⇧*[des] T1 ≡ T2.
#des elim des -des /2 width=2 by lifts_nil, ex_intro/
#d #e #des #IH #T1 elim (lift_total T1 d e)
#T #HT1 elim (IH T) -IH /3 width=4 by lifts_cons, ex_intro/
qed.
