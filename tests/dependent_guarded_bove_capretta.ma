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

inductive T : Prop :=
 | l : T
 | r : T-> T.

inductive Q : nat -> T -> Prop :=
 | lq : Q O l
 | lr : ∀n,t.Q (S (S n)) t -> Q n (r t). 
 
axiom F : False. 

definition xxx := λt.(match t return (λt:T.T) with 
    [ l => match F in False with [] 
    | r (t1:T) => t1]).
 
let rec f (n:nat) (t:T) on t :nat :=
  (match n with
  [ O => O
  | S mmm =>
    f (S (S mmm)) (xxx t)]).
 
let rec f (n:nat) (t:T) on t : Q n t -> nat :=
  (match n with
  [ O => λ_.O
  | S mmm => λq:Q (S mmm) (r t). 
    f (S (S mmm))
    (match t return (λt:T.T) with 
    [ l => match F in False with [] 
    | r (t1:T) => t1])
    
    (match q return λn,t,x.Q (S (S n)) t with 
     [ lq => match F in False return λ_.Q (S (S n)) t with [] 
     | lr k t qsskt => qsskt])
    ]). 
 
