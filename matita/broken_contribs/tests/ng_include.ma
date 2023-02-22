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

include "ng_pts.ma".
include "nat/plus.ma".

(*
ndefinition x ≝ O.
*)
(*ndefinition y ≝ cic:/matita/tests/ng_commands/x.def(1).*)

axiom P: nat → Prop.

unification hint 0 (∀n. P (0 + n) = P n) .

ntheorem foo: ∀n. ∀H:(P (? + n) → Prop). ∀p:P n. H p → True.
 #n; #H; #p; #_; napply I;
nqed. 

naxiom nnn: nat.