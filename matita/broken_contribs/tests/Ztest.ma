(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "arithmetics/nat.ma".

ninductive Z : Type ≝
  OZ : Z
| pos : nat → Z
| neg : nat → Z.

interpretation "Integers" 'Z = Z.

(* TODO: move the following two to datatypes/compare.ma *)
ninductive compare : Type[0] ≝
| LT : compare
| EQ : compare
| GT : compare.

nlet rec nat_compare n m: compare ≝
match n with
[ O ⇒ match m with 
      [ O ⇒ EQ
      | (S q) ⇒ LT ]
| S p ⇒ match m with 
      [ O ⇒ GT
      | S q ⇒ nat_compare p q]].

ndefinition Zplus : Z → Z → Z ≝
  λx,y. match x with
    [ OZ ⇒ y
    | pos m ⇒
        match y with
         [ OZ ⇒ x
         | pos n ⇒ (pos (pred ((S m)+(S n))))
         | neg n ⇒ 
              match nat_compare m n with
                [ LT ⇒ (neg (pred (n-m)))
                | EQ ⇒ OZ
                | GT ⇒ (pos (pred (m-n)))] ]
    | neg m ⇒
        match y with
         [ OZ ⇒ x
         | pos n ⇒
              match nat_compare m n with
                [ LT ⇒ (pos (pred (n-m)))
                | EQ ⇒ OZ
                | GT ⇒ (neg (pred (m-n)))]     
         | neg n ⇒ (neg (pred ((S m)+(S n))))] ].

interpretation "integer plus" 'plus x y = (Zplus x y).

ndefinition Z_of_nat ≝
λn. match n with
[ O ⇒ OZ 
| S n ⇒ pos n].

nlemma fails : ∀p. p + Z_of_nat 1 = Z_of_nat 1 + p.
#p;nnormalize;
