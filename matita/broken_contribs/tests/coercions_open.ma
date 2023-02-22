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



include "logic/equality.ma".
include "nat/nat.ma".

axiom A : nat -> Type.
axiom B : nat -> Type.
axiom AB : \forall x. A  x = B x.

axiom eatA : ∀n. A n -> A O.
axiom eatB : ∀n. B n -> A O.

axiom jmcBA : ∀n,m.∀p:A n = B m.B m -> A n. 
axiom jmcAB : ∀n,m.∀p:A n = B m.A n -> B m.

coercion cic:/matita/tests/coercions_open/jmcAB.con.
coercion cic:/matita/tests/coercions_open/jmcBA.con.

axiom daemon : ∀x,y:A O.x = y.

alias num (instance 0) = "natural number".
lemma xx : ∀b:B 2.∀a:A 1.eatA ? b = eatB ? a.
intros; [3,5,7,9: apply AB|1: apply daemon];skip.
qed.
