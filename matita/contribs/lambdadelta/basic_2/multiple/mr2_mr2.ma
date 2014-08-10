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

include "basic_2/multiple/mr2.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

(* Main properties **********************************************************)

theorem at_mono: ∀des,i,i1. @⦃i, des⦄ ≡ i1 → ∀i2. @⦃i, des⦄ ≡ i2 → i1 = i2.
#des #i #i1 #H elim H -des -i -i1
[ #i #x #H <(at_inv_nil … H) -x //
| #des #d #e #i #i1 #Hid #_ #IHi1 #x #H
  lapply (at_inv_cons_lt … H Hid) -H -Hid /2 width=1 by/
| #des #d #e #i #i1 #Hdi #_ #IHi1 #x #H
  lapply (at_inv_cons_ge … H Hdi) -H -Hdi /2 width=1 by/
]
qed-.
