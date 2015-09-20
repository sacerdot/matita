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

include "preamble.ma".

(* RELATIONS **********************************************************)

definition u0_predicate1: Type[0] → Type[1] ≝ λT.T → Prop.

definition u0_predicate2: Type[0] → Type[1] ≝ λT.T → u0_predicate1 T.

definition u1_predicate1: Type[1] → Type[2] ≝ λT.T → Prop.

definition u0_quantifier: Type[0] → Type[2] ≝ λT. u1_predicate1 (u0_predicate1 T).

record is_u0_reflexive (T:Type[0]) (All:u0_quantifier T) (R:u0_predicate2 T): Prop ≝
{
   u0_refl: All (λa. R a a)
}.

record can_u0_replace1 (T:Type[0]) (All:u0_quantifier T) (Q:u0_predicate2 T) (R:u0_predicate1 T): Prop ≝
{
   u0_repl1: All (λa. R a → All (λb. Q b a → R b))
}.
(*
record can_u0_replac2 (T:Type[0]) (All:u0_quantifier T) (Q:u0_predicate2 T) (R:u0_predicate2 T): Prop ≝
{
   u0_reflexivity: All (λa. R a a)
}.
*)
