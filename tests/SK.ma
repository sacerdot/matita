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

set "baseuri" "cic:/matita/SK/".

include "legacy/coq.ma".
alias symbol "eq" = "Coq's leibnitz's equality".

theorem SKK:
  \forall A:Set.
  \forall app: A \to A \to A.
  \forall K:A. 
  \forall S:A.
  \forall H1: (\forall x,y:A.(app (app K x) y) = x).
  \forall H2: (\forall x,y,z:A.
    (app (app (app S x) y) z) = (app (app x z) (app y z))).
  \forall x:A.
    (app (app (app S K) K) x) = x.
intros.auto paramodulation.
qed.

theorem bool1:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  (inv zero) = one.
intros.auto paramodulation.
qed.
  
theorem bool2:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero).
  \forall x:A. (mult x zero) = zero.
intros.auto paramodulation.
qed.

theorem bool3:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero).
  \forall x:A. (inv (inv x)) = x.
intros.auto paramodulation.
qed.
  
theorem bool2:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.auto paramodulation.
qed.
