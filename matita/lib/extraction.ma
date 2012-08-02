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

include "arithmetics/nat.ma".

(*FEATURE: kind signatures in type declarations*)

axiom Nat: Type[0].
axiom S: Nat → Nat.
axiom O: Nat.

axiom test1: Type[1].

axiom test2: Type[1] → Type[1].

axiom test3: Prop → Type[1] → CProp[1] → Type[1] → Type[2].

(* not in F_omega ? *)
axiom test4: ∀A:Type[1]. A → ∀B:Type[1]. B → ∀C:Prop. C → Type[1].

axiom test4': ∀C:Prop. C → C.

axiom test4'': ∀C:Prop. C → Nat.

axiom test4''': ∀C:Type[1]. C.

axiom test4_5: (∀A:Type[0].A) → Nat.

axiom test5: (Type[1] → Type[1]) → Type[1].

(* no content *)
axiom test6: Type[1] → Prop.

definition dtest1: Type[1] ≝ Nat → Nat.

definition dtest2: Type[2] ≝ ∀A:Type[1]. A → A.

definition dtest3: Type[1] → Type[1] ≝ λA:Type[1]. A → A.

definition dtest4: Type[1] → Type[1] ≝ λA:Type[1].dtest3 A.

definition dtest5: Type[1] → Type[1] ≝ dtest3.

definition dtest6: Type[1] ≝ dtest3 Nat.

(* no content *)
definition dtest7: Prop ≝ True → True.

(* no content *)
definition dtest8: Type[1] ≝ dtest3 True.

(* no content *)
definition dtest9: Type[1] ≝ dtest3 Prop.

definition dtest10: Type[1] → Type[1] → Type[1] ≝ λX,Y.X.

definition dtest11: Type[1] → Nat → Type[1] → Type[1] ≝ λ_:Type[1].λ_:Nat.λX:Type[1]. X → Nat → test1.


definition dtest12 ≝ λ_:Type[1].λ_:Nat.λX:Type[1]. X → Nat → test1.

definition dtest13 ≝ dtest3 Nat → dtest3 True → dtest3 Prop → Nat.

definition dtest14 ≝ λX:Type[2]. X → X.

(*FEATURE: type the forall bound variables*)
definition dtest15 ≝ ∀T:Type[1] → Type[1]. T Nat → T Nat.

definition dtest16 ≝ ∀T:Type[1]. T → Nat.

definition dtest17 ≝ ∀T:dtest14 Type[1]. T Nat → dtest14 Nat → dtest14 Nat.

definition dtest18 ≝ λA,B:Type[0].λn:Nat.λC:Type[0].A.

definition dtest19 ≝ dtest18 Nat True O Nat → dtest18 Nat Nat O Nat.

definition dtest20 ≝ test5 test2.

(*BUG: lambda-lift the inner declaration;
  to be traced, raises NotInFOmega; why? *)
definition dtest21 ≝ test5 (λX:Type[1].X).

definition ttest1 ≝ λx:Nat.x.

(*BUG: clash of name due to capitalisation*)
(*definition Ttest1 ≝ λx:Nat.x.*)

(*FEATURE: print binders in the l.h.s. without using lambda abstraction*)
definition ttest2 ≝ λT:Type[1].λx:T.x.

definition ttest3 ≝ λT:Type[1].λx:T.let y ≝ x in y.

definition ttest4 ≝ λT:Type[1].let y ≝ T in λx:y.x.

(*BUG IN HASKELL PRETTY PRINTING: all lets are let rec*)
(*definition ttest5 ≝ λT:Type[1].λy:T.let y ≝ y in y.*)

definition ttest6 ≝ ttest4 Nat.

definition ttest7 ≝ λf:∀X:Type[1].X. f (Nat → Nat) O.

definition ttest8 ≝ λf:∀X:Type[1].X. f (True → True) I.

definition ttest9 ≝ λf:∀X:Type[1].X. f (True → Nat) I.

definition ttest10 ≝ λf:∀X:Type[1].X. f (True → Nat → Nat) I O.

definition ttest11_aux ≝ λS:Type[1]. S → Nat.

definition ttest11 ≝ λf:ttest11_aux True. f I.

(*BUG here: requires F_omega eat_args*)
definition ttest12 ≝ λf:True → Nat. f I.

(*GENERAL BUG: name clashes when binders shadow each other in CIC*)