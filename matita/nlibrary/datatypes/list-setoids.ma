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

include "datatypes/list.ma".
include "sets/setoids.ma".

nlet rec eq_list (A : setoid) (l1, l2 : list A) on l1 : CProp[0] ≝ 
match l1 with
[ nil ⇒ match l2 return λ_.CProp[0] with [ nil ⇒ True | _ ⇒ False ]
| cons x xs ⇒ match l2 with [ nil ⇒ False | cons y ys ⇒ x = y ∧ eq_list ? xs ys]].
   
interpretation "eq_list" 'eq_low a b = (eq_list ? a b).
   
ndefinition LIST : setoid → setoid.
#S; @(list S); @(eq_list S);
##[ #l; nelim l; //; #; @; //;
##| #l1; nelim l1; ##[ #y; ncases y; //] #x xs H y; ncases y; ##[*] #y ys; *; #; @; /2/;
##| #l1; nelim l1; ##[ #l2 l3; ncases l2; ncases l3; /3/; #z zs y ys; *] 
    #x xs H l2 l3; ncases l2; ncases l3; /2/; #z zs y yz; *; #H1 H2; *; #H3 H4; @; /3/;##]
nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ S : setoid;
  T ≟ carr S,
  P1 ≟ refl ? (eq0 (LIST S)),
  P2 ≟ sym ? (eq0 (LIST S)),
  P3 ≟ trans ? (eq0 (LIST S)),
  X ≟ mk_setoid (list (carr S)) (mk_equivalence_relation ? (eq_list S) P1 P2 P3)
(*-----------------------------------------------------------------------*) ⊢
     carr X ≡ list T.

unification hint 0 ≔ S:setoid, a,b:list (carr S);
   R ≟ eq0 (LIST S),
   L ≟ (list (carr S))
(* -------------------------------------------- *) ⊢
   eq_list S a b ≡ eq_rel L R a b.

nlemma append_is_morph : ∀A:setoid.(list A) ⇒_0 (list A) ⇒_0 (list A).
#A; napply (mk_binary_morphism … (λs1,s2:list A. s1 @ s2)); #a; nelim a;
##[ #l1 l2 l3 defl1 El2l3; ncases l1 in defl1; ##[#;nassumption] #x xs; *;
##| #x xs IH l1 l2 l3 defl1 El2l3; ncases l1 in defl1; ##[ *] #y ys; *; #; /3/]
nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type0".
unification hint 0 ≔ S:setoid, A,B:list (carr S);
    SS ≟ carr S,
    MM ≟ mk_unary_morphism ?? (λA:list (carr S).
            mk_unary_morphism ?? 
              (λB:list (carr S).A @ B) (prop1 ?? (fun1 ??(append_is_morph S) A)))
          (prop1 ?? (append_is_morph S)),
    T ≟ LIST S
(*--------------------------------------------------------------------------*) ⊢
   fun1 T T (fun1 T (unary_morph_setoid T T) MM A) B ≡ append SS A B.


(* XXX to understand if are always needed or only if the coercion is active *)
include "sets/setoids1.ma".

unification hint 0 ≔ SS : setoid;
  S ≟ carr SS,
  TT ≟ setoid1_of_setoid (LIST SS)
(*-----------------------------------------------------------------*) ⊢ 
  list S ≡ carr1 TT.

alias symbol "hint_decl" (instance 1) = "hint_decl_CProp2".
unification hint 0 ≔ S : setoid, x,y;
  SS ≟ LIST S,
  TT ≟ setoid1_of_setoid SS
(*-----------------------------------------*) ⊢ 
  eq_list S x y ≡ eq_rel1 ? (eq1 TT) x y.    
    