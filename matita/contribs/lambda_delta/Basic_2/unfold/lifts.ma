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

include "Basic_2/grammar/term_vector.ma".
include "Basic_2/substitution/lift.ma".

(* GENERIC RELOCATION *******************************************************)

let rec ss (des:list2 nat nat) ≝ match des with
[ nil2          ⇒ ⟠
| cons2 d e des ⇒ {d + 1, e} :: ss des
].

inductive lifts: list2 nat nat → relation term ≝
| lifts_nil : ∀T. lifts ⟠ T T
| lifts_cons: ∀T1,T,T2,des,d,e.
              ⇑[d,e] T1 ≡ T → lifts des T T2 → lifts ({d, e} :: des) T1 T2
.

interpretation "generic relocation" 'RLift des T1 T2 = (lifts des T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lifts_inv_nil_aux: ∀T1,T2,des. ⇑[des] T1 ≡ T2 → des = ⟠ → T1 = T2.
#T1 #T2 #des * -T1 -T2 -des //
#T1 #T #T2 #d #e #des #_ #_ #H destruct
qed.

lemma lifts_inv_nil: ∀T1,T2. ⇑[⟠] T1 ≡ T2 → T1 = T2.
/2 width=3/ qed-.

fact lifts_inv_cons_aux: ∀T1,T2,des. ⇑[des] T1 ≡ T2 →
                         ∀d,e,tl. des = {d, e} :: tl →
                         ∃∃T. ⇑[d, e] T1 ≡ T & ⇑[tl] T ≡ T2.
#T1 #T2 #des * -T1 -T2 -des
[ #T #d #e #tl #H destruct
| #T1 #T #T2 #des #d #e #HT1 #HT2 #hd #he #tl #H destruct
  /2 width=3/
qed.

lemma lifts_inv_cons: ∀T1,T2,d,e,des. ⇑[{d, e} :: des] T1 ≡ T2 →
                      ∃∃T. ⇑[d, e] T1 ≡ T & ⇑[des] T ≡ T2.
/2 width=3/ qed-.

lemma lifts_inv_bind1: ∀I,T2,des,V1,U1. ⇑[des] 𝕓{I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⇑[des] V1 ≡ V2 & ⇑[ss des] U1 ≡ U2 &
                                T2 = 𝕓{I} V2. U2.
#I #T2 #des elim des -des
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5/
| #d #e #des #IHdes #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_bind1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHdes … HT2) -IHdes -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5/
]
qed-.

lemma lifts_inv_flat1: ∀I,T2,des,V1,U1. ⇑[des] 𝕗{I} V1. U1 ≡ T2 →
                       ∃∃V2,U2. ⇑[des] V1 ≡ V2 & ⇑[des] U1 ≡ U2 &
                                T2 = 𝕗{I} V2. U2.
#I #T2 #des elim des -des
[ #V1 #U1 #H
  <(lifts_inv_nil … H) -H /2 width=5/
| #d #e #des #IHdes #V1 #U1 #H
  elim (lifts_inv_cons … H) -H #X #H #HT2
  elim (lift_inv_flat1 … H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHdes … HT2) -IHdes -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lifts_simple_dx: ∀T1,T2,des. ⇑[des] T1 ≡ T2 → 𝕊[T1] → 𝕊[T2].
#T1 #T2 #des #H elim H -T1 -T2 -des // /3 width=5 by lift_simple_dx/
qed-.

lemma lifts_simple_sn: ∀T1,T2,des. ⇑[des] T1 ≡ T2 → 𝕊[T2] → 𝕊[T1].
#T1 #T2 #des #H elim H -T1 -T2 -des // /3 width=5 by lift_simple_sn/
qed-.

(* Basic properties *********************************************************)

lemma lifts_bind: ∀I,T2,V1,V2,des. ⇑[des] V1 ≡ V2 →
                  ∀T1. ⇑[ss des] T1 ≡ T2 →
                  ⇑[des] 𝕓{I} V1. T1 ≡ 𝕓{I} V2. T2.
#I #T2 #V1 #V2 #des #H elim H -V1 -V2 -des
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #des #d #e #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3/
]
qed.

lemma lifts_flat: ∀I,T2,V1,V2,des. ⇑[des] V1 ≡ V2 →
                  ∀T1. ⇑[des] T1 ≡ T2 →
                  ⇑[des] 𝕗{I} V1. T1 ≡ 𝕗{I} V2. T2.
#I #T2 #V1 #V2 #des #H elim H -V1 -V2 -des
[ #V #T1 #H >(lifts_inv_nil … H) -H //
| #V1 #V #V2 #des #d #e #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons … H) -H /3 width=3/
]
qed.

lemma lifts_total: ∀des,T1. ∃T2. ⇑[des] T1 ≡ T2.
#des elim des -des /2 width=2/
#d #e #des #IH #T1
elim (lift_total T1 d e) #T #HT1
elim (IH T) -IH /3 width=4/
qed.
