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

include "logic/equality.ma".
include "nat/nat.ma".

universe constraint Type[0] < Type[1].
universe constraint Type[1] < Type[2].
universe constraint CProp[0] < CProp[1].
universe constraint Type[0] ≤ CProp[0].
universe constraint CProp[0] ≤ Type[0].
universe constraint Type[1] ≤ CProp[1].
universe constraint CProp[1] ≤ Type[1].

ninductive A : Type[0] ≝ 
 | K : nat → A
 | W : nat → A.
 
nlet rec A_rect (Q_:∀x_3:A.Type[0]) H_K H_W x_3 on x_3 :Q_ x_3≝
match x_3 with [K x_4⇒H_K x_4|W x_5⇒H_W x_5].

nlemma yy : ∀x,y. K x = W y → False.
#x; #y; #H; 
nchange with 
  (match K x return λ_.Prop with [ K _ ⇒ False | W _ ⇒ True]);
nrewrite > H; nwhd; napply I;
nqed.  
  
nlemma xx : ∀x,y. K x = K y → x = y.
# x; #y; #H;
nchange with 
  (match K x return λ_.Prop with [ K a ⇒ a = y | W b ⇒ b = y]);
nrewrite > H; nwhd; napply (refl_eq ??);
nqed.

naxiom P : Prop.

nlemma ww : ∀a,b:A. a = b → P.
#a; #b;
ncases a; ncases b;
#x; #y; #H;
##[  

##| nelim (yy ?? H);
##| nelim (yy ?? H);

##]



  
