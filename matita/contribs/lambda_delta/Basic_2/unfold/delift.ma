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

include "Basic_2/unfold/tpss.ma".

(* DELIFT ON TERMS **********************************************************)

definition delift: nat → nat → lenv → relation term ≝
                   λd,e,L,T1,T2. ∃∃T. L ⊢ T1 [d, e] ≫* T & ↑[d, e] T2 ≡ T.

interpretation "delift (term)"
   'TSubst L T1 d e T2 = (delift d e L T1 T2).