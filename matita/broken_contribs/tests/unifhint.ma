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

include "nat/nat.ma".
include "list/list.ma".

inductive Expr : Type ≝
  | Evar : nat → Expr
  | Eopp : Expr → Expr
  | Eunit : Expr
  | Emult : Expr → Expr → Expr.
  
let rec sem (g : group) (e : Expr) (gamma : list (gcarr g)) on e : gcarr g ≝ 
  match e with
  [ Evar n ⇒ nth ? gamma 𝟙 n
  | Eopp x ⇒ (sem g x gamma) ^ -1
  | Eunit ⇒ 𝟙
  | Emult x y ⇒ (sem g x gamma) * (sem g y gamma)].
  
notation "〚term 19 x, term 19 g〛" non associative with precedence 90 
for @{ 'sem $x $g}.
interpretation "unif hint sem" 'sem x g = (sem _ x g). 
  
axiom P : ∀g:group. gcarr g → Prop.
axiom tac : Expr → Expr.
axiom start : ∀g,x,G.P g 〚x,G〛 → Prop.

notation > "ident a ≟ term 90 b term 20 c" 
non associative with precedence 90 for 
@{ let ${ident a} ≝ $b in $c }.

unification hint 0 (∀g:group.∀x:Expr.∀G:list (gcarr g). 
           V ≟ 〚x,G〛
(* ------------------------------------ *)
       〚Eopp x,G〛 = V^-1).


unification hint 0 (∀g:group.∀x,y.∀G:list (gcarr g). 

       V1 ≟ 〚x,G〛        V2 ≟ 〚y,G〛
(* ------------------------------------ *) 
           〚Emult x y,G〛 = V1 * V2).
        
unification hint 0 (∀g:group.∀G:list (gcarr g). 

(* ------------------------------------ *)
              〚Eunit,G〛 = 𝟙).

unification hint 2 (∀g:group.∀G:list (gcarr g).∀x:gcarr g. 

                   V ≟ x 
(* ------------------------------------ *)
          〚(Evar 0), (x :: G)〛 = V).
  
unification hint 3 (∀g:group.∀G:list (gcarr g).∀n.∀x:gcarr g.

               V ≟ 〚Evar n, G〛 
(* ------------------------------------ *)  
       〚(Evar (S n)), (x :: G)〛 = V) .
       
(* Esempio banale di divergenza       
unification hint 0 (∀g:group.∀G:list (gcarr g).∀x.
     V ≟ 〚x,G〛 
 ------------------------------------      
      〚x,G〛 = V).
*)

include "nat/plus.ma".
unification hint 0 (∀x,y.S x + y = S (x + y)).

axiom T : nat → Prop.
axiom F : ∀n,k.T (S (n + k)) → Prop. 
lemma diverge: ∀k,k1.∀h:T (? + k).F ? k1 h. 
    ?+k    = S(?+k1)
    S?1 + k   S(?1+k1)
    
lemma test : ∀g:group.∀x,y:gcarr g. ∀h:P ? ((𝟙 * x) * (x^-1 * y)). 
   start g ? ? h.

lemma test : ∀g:group.∀x,y:gcarr g. ∀h:P ? ((𝟙 * x) * (x^-1 * y)). 
   start g ? ? h.
 
   y == [| ?, x::? |]  
   
   〚Evar n, G〛 
   
   
   int: 〚(Evar (S n)), (x :: G)〛 = 〚Evar n, G〛
                             nth (m) (G)          = 〚Evar n, G〛


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
