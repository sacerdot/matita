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



include "nat/nat.ma".

axiom A : Type.

inductive vec : nat -> Type := 
 | vnil : vec O
 | vcons : ∀x:A.∀n:nat. vec n -> vec (S n).

definition f := λx,n.λv:vec n.vcons x n v.
definition g := λn,x.λv:vec n.vcons x n v.

include "logic/equality.ma".

(* definition xx :=  f = g. *)
theorem xx1 : ∀n.∀x1:vec n.f ? ? x1 = g ? ? x1.
