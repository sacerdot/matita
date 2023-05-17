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

include "ground/arith/int.ma".

(* DISCRIMINATOR FOR INTEGERS ***********************************************)

definition zsplit (A:Type[0]) (f1) (a) (f2) (z): A ≝
match z with
[ zneg  p ⇒ f1 p
| zzero   ⇒ a
| zpos  p ⇒ f2 p
].
