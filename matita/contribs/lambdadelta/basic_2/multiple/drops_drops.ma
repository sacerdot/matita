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

include "basic_2/multiple/drops_drop.ma".

(* ITERATED LOCAL ENVIRONMENT SLICING ***************************************)

(* Main properties **********************************************************)

(* Basic_1: was: drop1_trans *)
theorem drops_trans: ∀L,L2,s,des2. ⇩*[s, des2] L ≡ L2 → ∀L1,des1. ⇩*[s, des1] L1 ≡ L →
                     ⇩*[s, des2 @@ des1] L1 ≡ L2.
#L #L2 #s #des2 #H elim H -L -L2 -des2 /3 width=3 by drops_cons/
qed-.
