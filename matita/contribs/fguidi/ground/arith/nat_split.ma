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

include "ground/arith/nat.ma".

(* DISCRIMINATOR FOR NON-NEGATIVE INTEGERS **********************************)

definition nsplit (A:Type[0]) (a) (f) (n): A ≝
match n with
[ nzero   ⇒ a
| npos  p ⇒ f p
].
