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

include "datatypes/pairs.ma".
include "sets/setoids.ma".

nlet rec eq_pair (A, B : setoid) (a : A × B) (b : A × B) on a : CProp[0] ≝ 
  match a with [ mk_pair a1 a2 ⇒ 
  match b with [ mk_pair b1 b2 ⇒ a1 = b1 ∧ a2 = b2 ]].

interpretation "eq_pair" 'eq_low a b = (eq_pair ?? a b). 

nlemma PAIR : ∀A,B:setoid. setoid.
#A B; @(A × B); @(eq_pair …);
##[ #ab; ncases ab; #a b; @; napply #;
##| #ab cd; ncases ab; ncases cd; #a1 a2 b1 b2; *; #E1 E2;
    @; napply (?^-1); //;
##| #a b c; ncases a; ncases b; ncases c; #c1 c2 b1 b2 a1 a2;
    *; #E1 E2; *; #E3 E4; @; ##[ napply (.= E1); //] napply (.= E2); //.##]
nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ AA, BB;
    A ≟ carr AA, B ≟ carr BB,
    P1 ≟ refl ? (eq0 (PAIR AA BB)),
    P2 ≟ sym ? (eq0 (PAIR AA BB)),
    P3 ≟ trans ? (eq0 (PAIR AA BB)),
    R ≟ mk_setoid (A × B) (mk_equivalence_relation ? (eq_pair …) P1 P2 P3)
(*---------------------------------------------------------------------------*)⊢
    carr R ≡ A × B.
 
unification hint 0 ≔ S1,S2,a,b;
   R ≟ PAIR S1 S2,
   L ≟ pair (carr S1) (carr S2)
(* -------------------------------------------- *) ⊢
   eq_pair S1 S2 a b ≡ eq_rel L (eq0 R) a b.    

 