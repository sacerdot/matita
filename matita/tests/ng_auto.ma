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

universe constraint Type[0] < Type[1].
universe constraint Type[1] < Type[2].

naxiom T : Type[0].
naxiom P : T → T → CProp[0].
naxiom Q : T → CProp[0].
naxiom f : T → T → T.

naxiom f_com : ∀x,y. P (f x y) (f y x).
naxiom f_Q : ∀x,y. P x y → Q (f x y).

nlemma foo : ∀x,y. Q x → Q (f (f x y) (f y x)).
#x; #y; #H; 
ncut (Q x);
##[##2: #_; nauto;
##| nassumption;
##]
nqed.

naxiom And : CProp[0] → CProp[0] → CProp[0].
naxiom And_intro : ∀A,B.A → B → And A B.

naxiom zero : T.
naxiom succ : T → T.
naxiom is_nat : T → CProp[0].
naxiom is_nat_0 : is_nat zero.
naxiom is_nat_S : ∀x.is_nat x → is_nat (succ x).

nlemma bar : ∀P:T → CProp[0].P (succ zero) → (λx.And (is_nat x) (P x)) ?.
##[ #P; #H; nwhd; napply And_intro; ##] nauto.  
nqed.

naxiom A : CProp[0].
naxiom pA : A.

nlemma baz : ∀P,Q:CProp[0].(A → P) → (And A P → Q) → Q.
nauto depth=3;
nqed.

nlemma traz:
  ∀T:Type[0].
  ∀And: CProp[0] → CProp[0] → CProp[0] → CProp[0].
  ∀And_elim : ∀a,b,c.a → b → c → And a b c. 
  ∀C: T → T → T → CProp[0].
  ∀B: T → T → CProp[0].
  ∀A: T → CProp[0].
  ∀a,b,c:T.
  ∀p2:A b.
  ∀p1:A a.
  ∀p3:B a b. 
  ∀p3:B b b. 
  ∀p4:B b a.  
  ∀p3:B a a. 
  ∀p5:C a a a.
  (λx,y,z:T.And (A x) (B x y) (C x y z)) ???.
##[ #T; #And; #And_intro; #A; #B;  #C; #a;  #b; #p1; #p2; #p3; #p4; #p5;
    #p6; #p7; nauto;