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

record group : Type β {
  gcarr :> Type;
  gmult : gcarr β gcarr β gcarr; 
  gopp  : gcarr β gcarr;
  gunit : gcarr
}.

interpretation "unif hints inverse" 'invert x = (gopp _ x).
interpretation "unif hing times" 'times x y = (gmult _ x y).
notation "π" non associative with precedence 90 for @{ 'unit }.
interpretation "unif hint unit" 'unit = (gunit _).

include "nat/nat.ma".
include "list/list.ma".

inductive Expr : Type β
  | Evar : nat β Expr
  | Eopp : Expr β Expr
  | Eunit : Expr
  | Emult : Expr β Expr β Expr.
  
let rec sem (g : group) (e : Expr) (gamma : list (gcarr g)) on e : gcarr g β 
  match e with
  [ Evar n β nth ? gamma π n
  | Eopp x β (sem g x gamma) ^ -1
  | Eunit β π
  | Emult x y β (sem g x gamma) * (sem g y gamma)].
  
notation "γterm 19 x, term 19 gγ" non associative with precedence 90 
for @{ 'sem $x $g}.
interpretation "unif hint sem" 'sem x g = (sem _ x g). 
  
axiom P : βg:group. gcarr g β Prop.
axiom tac : Expr β Expr.
axiom start : βg,x,G.P g γx,Gγ β Prop.

notation > "ident a β term 90 b term 20 c" 
non associative with precedence 90 for 
@{ let ${ident a} β $b in $c }.

unification hint 0 (βg:group.βx:Expr.βG:list (gcarr g). 
           V β γx,Gγ
(* ------------------------------------ *)
       γEopp x,Gγ = V^-1).


unification hint 0 (βg:group.βx,y.βG:list (gcarr g). 

       V1 β γx,Gγ        V2 β γy,Gγ
(* ------------------------------------ *) 
           γEmult x y,Gγ = V1 * V2).
        
unification hint 0 (βg:group.βG:list (gcarr g). 

(* ------------------------------------ *)
              γEunit,Gγ = π).

unification hint 2 (βg:group.βG:list (gcarr g).βx:gcarr g. 

                   V β x 
(* ------------------------------------ *)
          γ(Evar 0), (x :: G)γ = V).
  
unification hint 3 (βg:group.βG:list (gcarr g).βn.βx:gcarr g.

               V β γEvar n, Gγ 
(* ------------------------------------ *)  
       γ(Evar (S n)), (x :: G)γ = V) .
       
(* Esempio banale di divergenza       
unification hint 0 (βg:group.βG:list (gcarr g).βx.
     V β γx,Gγ 
 ------------------------------------      
      γx,Gγ = V).
*)

include "nat/plus.ma".
unification hint 0 (βx,y.S x + y = S (x + y)).

axiom T : nat β Prop.
axiom F : βn,k.T (S (n + k)) β Prop. 
lemma diverge: βk,k1.βh:T (? + k).F ? k1 h. 
    ?+k    = S(?+k1)
    S?1 + k   S(?1+k1)
    
lemma test : βg:group.βx,y:gcarr g. βh:P ? ((π * x) * (x^-1 * y)). 
   start g ? ? h.

lemma test : βg:group.βx,y:gcarr g. βh:P ? ((π * x) * (x^-1 * y)). 
   start g ? ? h.
 
   y == [| ?, x::? |]  
   
   γEvar n, Gγ 
   
   
   int: γ(Evar (S n)), (x :: G)γ = γEvar n, Gγ
                             nth (m) (G)          = γEvar n, Gγ


βx,Ξ. [| B 0, x::Ξ |] = x
βn,y,Ξ. [| B n, Ξ |] = [| B (S n), y::Ξ |] 
βe,f. [| Add e f, Ξ |] = [| e, Ξ |] + [| f, Ξ |]


x + x = [| ?1, ?2 |]

x = [| ?1,?2 |]
?1 β B 0
?2 β x::?3

x = [| ?4, y::x::?3 |]

[| ?4, x::?3 |] =?= [| B (S ?n), ?y::?Ξ |]
x =?= [| B ?n, ?Ξ |]


x  =?=   E

x  =?=  ?,   ? =?= E
