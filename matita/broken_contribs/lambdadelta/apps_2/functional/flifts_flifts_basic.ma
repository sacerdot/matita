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

include "apps_2/functional/flifts_flifts.ma".
include "apps_2/functional/flifts_basic.ma".

(* BASIC FUNCTIONAL RELOCATION **********************************************)

(* Main properties **********************************************************)

theorem flifts_basic_swap (T) (d1) (d2) (h1) (h2):
                          d2 ≤ d1 → ↑[d2,h2]↑[d1,h1]T = ↑[h2+d1,h1]↑[d2,h2]T.
/3 width=1 by flifts_comp, basic_swap/ qed-.
(*
lemma flift_join: ∀e1,e2,T. ⇧[e1,e2] ↑[0,e1] T ≡ ↑[0,e1 + e2] T.
#e1 #e2 #T
lapply (flift_lift T 0 (e1+e2)) #H
elim (lift_split … H e1 e1) -H // #U #H
>(flift_inv_lift … H) -H //
qed.
*)
