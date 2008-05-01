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


include "coq.ma".

inductive nat : Set \def
   O : nat
 | S : nat \to nat.


inductive le (n:nat) : nat \to Prop \def
   leO : le n n
 | leS : \forall m. le n m \to le n (S m).
 
theorem le_inv2:
 \forall n,m.
  \forall P: nat -> nat -> Prop.
   ? -> ? -> le n m -> P n m.
[7:
  intros;
  inversion H;
  [ apply x
  | simplify;
    apply x1
  ]
| skip
| skip
| skip
| skip
| skip
| skip
]
qed.

inductive ledx : nat \to nat \to Prop \def
   ledxO : \forall n. ledx n n
 | ledxS : \forall m.\forall n. ledx n m \to ledx n (S m).


alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".

theorem test_inversion: \forall n. le n O \to n=O.
 intros.
 inversion H.
 (* cut n=n \to O=O \to n=O.
  apply Hcut; reflexivity. *)
  (* elim H. BUG DI UNSHARING *)
  (*apply (ledx_ind (\lambda x.\lambda y.  n=x \to O=y \to x=y) ? ? ? ? H).*)
    simplify. intros. reflexivity.    
    simplify. intros. destruct H3.
qed.
