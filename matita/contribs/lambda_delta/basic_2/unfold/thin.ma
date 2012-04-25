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

include "basic_2/unfold/ltpss.ma".

(* DELIFT ON LOCAL ENVIRONMENTS  ********************************************)

definition thin: nat → nat → relation lenv ≝
                 λd,e,L1,L2. ∃∃L. L1 [d, e] ▶* L & ⇩[d, e] L ≡ L2.

interpretation "delift (local environment)"
   'TSubst L1 d e L2 = (thin d e L1 L2).

(* Basic properties *********************************************************)
