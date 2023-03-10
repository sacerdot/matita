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

record group : Type â {
  gcarr :> Type;
  gmult : gcarr â gcarr â gcarr; 
  gopp  : gcarr â gcarr;
  gunit : gcarr
}.

interpretation "unif hints inverse" 'invert x = (gopp _ x).
interpretation "unif hing times" 'times x y = (gmult _ x y).
notation "đ" non associative with precedence 90 for @{ 'unit }.
interpretation "unif hint unit" 'unit = (gunit _).

inductive Expr (g : group) : Type â
  | Evar : gcarr g â Expr g
  | Eopp : Expr g â Expr g
  | Eunit : Expr g
  | Emult : Expr g â Expr g â Expr g.
  
let rec sem (g : group) (e : Expr g) on e : gcarr g â 
  match e with
  [ Evar x â x
  | Eopp x â (sem g x) ^ -1
  | Eunit â đ
  | Emult x y â (sem g x) * (sem g y)].
  
notation "ăxă" non associative with precedence 90 for @{ 'sem $x }.
interpretation "unif hint sem" 'sem x = (sem _ x). 
  
axiom P : âg:group. gcarr g â Prop.
axiom tac : âg:group. Expr g â Expr g.
axiom start : âg,x.P g ăxă â Prop.


include "logic/equality.ma".

notation "@ t" non associative with precedence 90 for @{ (Îťx.x) $t }.

unification hint (âg:group.âx:g. ăEvar ? xă = x).
unification hint (âg:group.âx. ăEopp g xă = (@ăxă) ^-1).
unification hint (âg:group.âx,y. ăEmult g x yă = (@ăxă) * (@ăyă)).

lemma test : âg:group.âx,y:g. âh:P ? (x * (x^-1 * y)). start g ? h.
 


âx,Î. [| B 0, x::Î |] = x
ân,y,Î. [| B n, Î |] = [| B (S n), y::Î |] 
âe,f. [| Add e f, Î |] = [| e, Î |] + [| f, Î |]


x + x = [| ?1, ?2 |]

x = [| ?1,?2 |]
?1 â B 0
?2 â x::?3

x = [| ?4, y::x::?3 |]

[| ?4, x::?3 |] =?= [| B (S ?n), ?y::?Î |]
x =?= [| B ?n, ?Î |]


x  =?=   E

x  =?=  ?,   ? =?= E