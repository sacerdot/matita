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

include "basic_2/multiple/lifts_lift.ma".

(* GENERIC RELOCATION *******************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: lift1_lift1 (left to right) *)
theorem lifts_trans: ∀T1,T,des1. ⇧*[des1] T1 ≡ T → ∀T2:term. ∀des2. ⇧*[des2] T ≡ T2 →
                     ⇧*[des1 @@ des2] T1 ≡ T2.
#T1 #T #des1 #H elim H -T1 -T -des1 // /3 width=3/
qed.
