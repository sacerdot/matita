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

set "baseuri" "cic:/matita/RELATIONAL/Zah/defs".

include "datatypes/constructors.ma".
include "logic/coimplication.ma".
include "NPlusList/defs.ma".

definition Zah \def Nat \times Nat.
(*
definition ZEq: Zah \to Zah -> Prop :=
   \lambda z1,z2.
   \forall n. ((\fst z1) + (\snd z2) == n) \liff (\fst z2) + (\snd z1) == n.

interpretation "integer equality" 'zeq x y =
 (cic:/matita/RELATIONAL/Zah/defs/ZEq.con x y).

notation "hvbox(a break = b)"
  non associative with precedence 45
for @{ 'zeq $a $b }.
*)