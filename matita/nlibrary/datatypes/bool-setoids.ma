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

include "datatypes/bool.ma".
include "sets/setoids.ma".

ndefinition eq_bool ≝ 
  λa,b.match a with 
       [ true  ⇒ match b with [ true ⇒ True  | _ ⇒ False ]
       | false ⇒ match b with [ false ⇒ True | _ ⇒ False ]].

 (* XXX move to bool *)
interpretation "bool eq" 'eq_low a b = (eq_bool a b). 

ndefinition BOOL : setoid.
@bool; @(eq_bool); #x; ncases x; //; #y; ncases y; //; #z; ncases z; //; nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
alias id "refl" = "cic:/matita/ng/properties/relations/refl.fix(0,1,3)".
unification hint 0 ≔ ;
  P1 ≟ refl ? (eq0 BOOL),
  P2 ≟ sym ? (eq0 BOOL),
  P3 ≟ trans ? (eq0 BOOL),
  X ≟ mk_setoid bool (mk_equivalence_relation ? (eq_bool) P1 P2 P3)
(*-----------------------------------------------------------------------*) ⊢
     carr X ≡ bool.

unification hint 0 ≔ a,b;
   R ≟ eq0 BOOL,
   L ≟ bool
(* -------------------------------------------- *) ⊢
   eq_bool a b ≡ eq_rel L R a b.
