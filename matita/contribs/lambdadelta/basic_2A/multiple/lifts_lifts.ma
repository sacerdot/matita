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

include "ground/relocation/mr2_append.ma".
include "basic_2A/multiple/lifts_lift.ma".

(* GENERIC RELOCATION *******************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: lift1_lift1 (left to right) *)
theorem lifts_trans: ∀T1,T,cs1. ⬆*[cs1] T1 ≡ T → ∀T2:term. ∀cs2. ⬆*[cs2] T ≡ T2 →
                     ⬆*[cs1 @@ cs2] T1 ≡ T2.
#T1 #T #cs1 #H elim H -T1 -T -cs1 /3 width=3 by lifts_cons/
qed.
