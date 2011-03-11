(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "lambda/par_reduction.ma".

(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T
. *)

inductive red : T →T → Prop ≝
  | rbeta: ∀P,M,N. red (App (Lambda P M) N) (M[0 ≝ N])
  | rdapp: ∀M,N. red (App (D M) N) (D (App M N))
  | rdlam: ∀M,N. red (Lambda M (D N)) (D (Lambda M N))
  | rappl: ∀M,M1,N. red M M1 → red (App M N) (App M1 N)
  | rappr: ∀M,N,N1. red N N1 → red (App M N1) (App M N1)
  | rlaml: ∀M,M1,N. red M M1 → red (Lambda M N) (Lambda M1 N)
  | rlamr: ∀M,N,N1. red N N1 → red(Lambda M N1) (Lambda M N1)
  | rprodl: ∀M,M1,N. red M M1 → red (Prod M N) (Prod M1 N)
  | rprodr: ∀M,N,N1. red N N1 → red (Prod M N1) (Prod M N1)
  | d: ∀M,M1. red M M1 → red (D M) (D M1).

lemma red_to_pr: ∀M,N. red M N → pr M N.
#M #N #redMN (elim redMN) /2/
qed.
 





