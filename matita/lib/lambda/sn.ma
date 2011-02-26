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

include "lambda/ext.ma".

(* saturation conditions on an explicit subset ********************************)

definition SAT0 ≝ λP. ∀l,n. all P l → P (Appl (Sort n) l).

definition SAT1 ≝ λP. ∀l,i. all P l → P (Appl (Rel i) l).

definition SAT2 ≝ λ(P:?→Prop). ∀F,A,B,l. P B → P A → 
                  P (Appl F[0:=A] l) → P (Appl (Lambda B F) (A::l)).

theorem SAT0_sort: ∀P,n. SAT0 P → P (Sort n).
#P #n #H @(H (nil ?) …) //
qed.

theorem SAT1_rel: ∀P,i. SAT1 P → P (Rel i).
#P #i #H @(H (nil ?) …) //
qed.

(* STRONGLY NORMALIZING TERMS *************************************************)

(* SN(t) holds when t is strongly normalizing *)
(* FG: we axiomatize it for now because we dont have reduction yet *)
axiom SN: T → Prop.

definition CR1 ≝ λ(P:?→Prop). ∀M. P M → SN M.

axiom sn_sort: SAT0 SN.

axiom sn_rel: SAT1 SN.

axiom sn_lambda: ∀B,F. SN B → SN F → SN (Lambda B F).

axiom sn_beta: SAT2 SN.

(* FG: do we need this?
axiom sn_lift: ∀t,k,p. SN t → SN (lift t p k).
*)
