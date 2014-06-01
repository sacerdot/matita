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

include "basic_2/substitution/lift_vector.ma".
include "basic_2/multiple/lifts.ma".

(* GENERIC TERM VECTOR RELOCATION *******************************************)

inductive liftsv (des:list2 nat nat) : relation (list term) ≝
| liftsv_nil : liftsv des (◊) (◊)
| liftsv_cons: ∀T1s,T2s,T1,T2.
               ⇧*[des] T1 ≡ T2 → liftsv des T1s T2s →
               liftsv des (T1 @ T1s) (T2 @ T2s)
.

interpretation "generic relocation (vector)"
   'RLiftStar des T1s T2s = (liftsv des T1s T2s).

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: lifts1_flat (left to right) *)
lemma lifts_inv_applv1: ∀V1s,U1,T2,des. ⇧*[des] Ⓐ V1s. U1 ≡ T2 →
                        ∃∃V2s,U2. ⇧*[des] V1s ≡ V2s & ⇧*[des] U1 ≡ U2 &
                                  T2 = Ⓐ V2s. U2.
#V1s elim V1s -V1s normalize
[ #T1 #T2 #des #HT12  
  @ex3_2_intro [3,4: // |1,2: skip | // ] (**) (* explicit constructor *)
| #V1 #V1s #IHV1s #T1 #X #des #H
  elim (lifts_inv_flat1 … H) -H #V2 #Y #HV12 #HY #H destruct
  elim (IHV1s … HY) -IHV1s -HY #V2s #T2 #HV12s #HT12 #H destruct
  @(ex3_2_intro) [4: // |3: /2 width=2 by liftsv_cons/ |1,2: skip | // ] (**) (* explicit constructor *)
]
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: lifts1_flat (right to left) *)
lemma lifts_applv: ∀V1s,V2s,des. ⇧*[des] V1s ≡ V2s →
                   ∀T1,T2. ⇧*[des] T1 ≡ T2 →
                   ⇧*[des] Ⓐ V1s. T1 ≡ Ⓐ V2s. T2.
#V1s #V2s #des #H elim H -V1s -V2s /3 width=1 by lifts_flat/
qed.
