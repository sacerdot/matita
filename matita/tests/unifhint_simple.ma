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

record group : Type ≝ {
  gcarr :> Type;
  gmult : gcarr → gcarr → gcarr; 
  gopp  : gcarr → gcarr;
  gunit : gcarr
}.

interpretation "unif hints inverse" 'invert x = (gopp _ x).
interpretation "unif hing times" 'times x y = (gmult _ x y).
notation "𝟙" non associative with precedence 90 for @{ 'unit }.
interpretation "unif hint unit" 'unit = (gunit _).

inductive Expr (g : group) : Type ≝
  | Evar : gcarr g → Expr g
  | Eopp : Expr g → Expr g
  | Eunit : Expr g
  | Emult : Expr g → Expr g → Expr g.
  
let rec sem (g : group) (e : Expr g) on e : gcarr g ≝ 
  match e with
  [ Evar x ⇒ x
  | Eopp x ⇒ (sem g x) ^ -1
  | Eunit ⇒ 𝟙
  | Emult x y ⇒ (sem g x) * (sem g y)].
  
notation "〚x〛" non associative with precedence 90 for @{ 'sem $x }.
interpretation "unif hint sem" 'sem x = (sem _ x). 
  
axiom P : ∀g:group. gcarr g → Prop.
axiom tac : ∀g:group. Expr g → Expr g.
axiom start : ∀g,x.P g 〚x〛 → Prop.


include "logic/equality.ma".

notation "@ t" non associative with precedence 90 for @{ (λx.x) $t }.

unification hint (∀g:group.∀x:g. 〚Evar ? x〛 = x).
unification hint (∀g:group.∀x. 〚Eopp g x〛 = (@〚x〛) ^-1).
unification hint (∀g:group.∀x,y. 〚Emult g x y〛 = (@〚x〛) * (@〚y〛)).

lemma test : ∀g:group.∀x,y:g. ∀h:P ? (x * (x^-1 * y)). start g ? h.
 


∀x,Γ. [| B 0, x::Γ |] = x
∀n,y,Γ. [| B n, Γ |] = [| B (S n), y::Γ |] 
∀e,f. [| Add e f, Γ |] = [| e, Γ |] + [| f, Γ |]


x + x = [| ?1, ?2 |]

x = [| ?1,?2 |]
?1 ≝ B 0
?2 ≝ x::?3

x = [| ?4, y::x::?3 |]

[| ?4, x::?3 |] =?= [| B (S ?n), ?y::?Γ |]
x =?= [| B ?n, ?Γ |]


x  =?=   E

x  =?=  ?,   ? =?= E