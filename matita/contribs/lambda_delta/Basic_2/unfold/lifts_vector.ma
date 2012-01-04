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

include "Basic_2/substitution/lift_vector.ma".
include "Basic_2/unfold/lifts.ma".

(* GENERIC RELOCATION *******************************************************)

inductive liftsv (des:list2 nat nat) : relation (list term) ≝
| liftsv_nil : liftsv des ◊ ◊
| liftsv_cons: ∀T1s,T2s,T1,T2.
               ⇑[des] T1 ≡ T2 → liftsv des T1s T2s →
               liftsv des (T1 :: T1s) (T2 :: T2s)
.

interpretation "generic relocation (vector)"
   'RLift des T1s T2s = (liftsv des T1s T2s).

(* Basic inversion lemmas ***************************************************)

axiom lifts_inv_applv1: ∀V1s,U1,T2,des. ⇑[des] Ⓐ V1s. U1 ≡ T2 →
                        ∃∃V2s,U2. ⇑[des] V1s ≡ V2s & ⇑[des] U1 ≡ U2 &
                                  T2 = Ⓐ V2s. U2.

(* Basic properties *********************************************************)

lemma liftsv_applv: ∀V1s,V2s,des. ⇑[des] V1s ≡ V2s →
                    ∀T1,T2. ⇑[des] T1 ≡ T2 →
                    ⇑[des] Ⓐ V1s. T1 ≡ Ⓐ V2s. T2.
#V1s #V2s #des #H elim H -V1s -V2s // /3 width=1/
qed.
