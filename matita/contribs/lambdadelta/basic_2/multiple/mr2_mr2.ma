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

theorem at_mono: ∀cs,i,i1. @⦃i, cs⦄ ≡ i1 → ∀i2. @⦃i, cs⦄ ≡ i2 → i1 = i2.
#cs #i #i1 #H elim H -cs -i -i1
[ #i #x #H <(at_inv_nil … H) -x //
| #cs #l #m #i #i1 #Hil #_ #IHi1 #x #H
  lapply (at_inv_cons_lt … H Hil) -H -Hil /2 width=1 by/
| #cs #l #m #i #i1 #Hli #_ #IHi1 #x #H
  lapply (at_inv_cons_ge … H Hli) -H -Hli /2 width=1 by/
]
qed-.
