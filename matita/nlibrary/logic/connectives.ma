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

include "logic/pts.ma".

inductive True: CProp[0] ≝
  I : True.

inductive False: CProp[0] ≝.

definition Not: CProp[0] → CProp[0] ≝
  λA. A → False.

interpretation "logical ot" 'not x = (Not x).

inductive And (A,B:CProp[0]) : CProp[0] ≝
    conj : A → B → And A B.

interpretation "logical and" 'and x y = (And x y).

inductive Or (A,B:CProp[0]) : CProp[0] ≝
     or_introl : A → Or A B
   | or_intror : B → Or A B.

interpretation "logical or" 'or x y = (Or x y).

inductive Ex (A:Type[0]) (P:A → CProp[0]) : CProp[0] ≝
    ex_intro: ∀x:A. P x → Ex A P.


inductive Ex1 (A:Type[1]) (P:A → CProp[0]) : CProp[1] ≝
    ex_intro1: ∀x:A. P x → Ex1 A P.

interpretation "exists1" 'exists x = (Ex1 ? x).
interpretation "exists" 'exists x = (Ex ? x).

inductive sigma (A : Type[0]) (P : A → CProp[0]) : Type[0] ≝ 
 sig_intro : ∀x:A.P x → sigma A P. 

interpretation "sigma" 'sigma \eta.p = (sigma ? p). 

record iff (A,B: CProp[0]) : CProp[0] ≝
 { if: A → B;
   fi: B → A
 }.

notation > "hvbox(a break \liff b)"
  left associative with precedence 25
for @{ 'iff $a $b }.

notation "hvbox(a break \leftrightarrow b)"
  left associative with precedence 25
for @{ 'iff $a $b }.

interpretation "logical iff" 'iff x y = (iff x y).
