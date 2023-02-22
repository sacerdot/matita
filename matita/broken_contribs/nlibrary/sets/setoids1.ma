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

include "properties/relations1.ma".
include "sets/setoids.ma".
include "hints_declaration.ma".

nrecord setoid1: Type[2] ≝ { 
  carr1:> Type[1];
  eq1: equivalence_relation1 carr1 
}.

unification hint 0 ≔ R : setoid1; 
   MR ≟ (carr1 R), 
   lock ≟ mk_lock2 Type[1] MR setoid1 R 
(* ---------------------------------------- *) ⊢ 
   setoid1 ≡ force2 ? MR lock.

notation < "[\setoid1\ensp\of term 19 x]" non associative with precedence 90 for @{'mk_setoid1 $x}.
interpretation "mk_setoid1" 'mk_setoid1 x = (mk_setoid1 x ?).

(* da capire se mettere come coercion *)
ndefinition setoid1_of_setoid: setoid → setoid1.
 #s; @ (carr s); @ (eq0…) (refl…) (sym…) (trans…);
nqed.

alias symbol "hint_decl" = "hint_decl_CProp2".
alias symbol "hint_decl" (instance 1) = "hint_decl_Type2".
unification hint 0 ≔ A,x,y;
   T  ≟ carr A, 
   R  ≟ setoid1_of_setoid A,
   T1 ≟ carr1 R
(*-----------------------------------------------*) ⊢
   eq_rel T (eq0 A) x y ≡ eq_rel1 T1 (eq1 R) x y.

unification hint 0 ≔ A;
   R  ≟ setoid1_of_setoid A
(*-----------------------------------------------*) ⊢
   carr A ≡ carr1 R.

interpretation "setoid1 eq" 'eq t x y = (eq_rel1 ? (eq1 t) x y).
interpretation "setoid eq" 'eq t x y = (eq_rel ? (eq0 t) x y).

notation > "hvbox(a break =_12 b)" non associative with precedence 45
for @{ eq_rel2 (carr2 (setoid2_of_setoid1 ?)) (eq2 (setoid2_of_setoid1 ?)) $a $b }.
notation > "hvbox(a break =_0 b)" non associative with precedence 45
for @{ eq_rel ? (eq0 ?) $a $b }.
notation > "hvbox(a break =_1 b)" non associative with precedence 45
for @{ eq_rel1 ? (eq1 ?) $a $b }.

interpretation "setoid1 symmetry" 'invert r = (sym1 ???? r).
interpretation "setoid symmetry" 'invert r = (sym ???? r).
notation ".=_1 r" with precedence 55 for @{'trans_x1 $r}.
interpretation "trans1" 'trans r = (trans1 ????? r).
interpretation "trans" 'trans r = (trans ????? r).
interpretation "trans1_x1" 'trans_x1 r = (trans1 ????? r).

nrecord unary_morphism1 (A,B: setoid1) : Type[1] ≝ { 
  fun11:1> A → B;
  prop11: ∀a,a'. eq1 ? a a' → eq1 ? (fun11 a) (fun11 a') 
}.
 
notation > "B ⇒_1 C" right associative with precedence 72 for @{'umorph1 $B $C}.
notation "hvbox(B break ⇒\sub 1 C)" right associative with precedence 72 for @{'umorph1 $B $C}.
interpretation "unary morphism 1" 'umorph1 A B = (unary_morphism1 A B).
 
notation "┼_1 c" with precedence 89 for @{'prop1_x1 $c }.
interpretation "prop11" 'prop1 c = (prop11 ????? c).
interpretation "prop11_x1" 'prop1_x1 c = (prop11 ????? c).
interpretation "refl1" 'refl = (refl1 ???).

ndefinition unary_morphism1_setoid1: setoid1 → setoid1 → setoid1.
 #s; #s1; @ (s ⇒_1 s1); @
     [ #f; #g; napply (∀a,a':s. a=a' → f a = g a')
     | #x; #a; #a'; #Ha; napply (.= †Ha); napply refl1
     | #x; #y; #H; #a; #a'; #Ha; napply (.= †Ha); napply sym1; /2/
     | #x; #y; #z; #H1; #H2; #a; #a'; #Ha; napply (.= †Ha); napply trans1; ##[##2: napply H1 | ##skip | napply H2]//;##]
nqed.

unification hint 0 ≔ S, T ;
   R ≟ (unary_morphism1_setoid1 S T)
(* --------------------------------- *) ⊢
   carr1 R ≡ unary_morphism1 S T.
   
notation "l ╪_1 r" with precedence 89 for @{'prop2_x1 $l $r }.
interpretation "prop21" 'prop2 l r = (prop11 ? (unary_morphism1_setoid1 ??) ? ?? l ?? r).
interpretation "prop21_x1" 'prop2_x1 l r = (prop11 ? (unary_morphism1_setoid1 ??) ? ?? l ?? r).

nlemma unary_morph1_eq1: ∀A,B.∀f,g: A ⇒_1 B. (∀x. f x = g x) → f = g.
/3/. nqed.

nlemma mk_binary_morphism1:
 ∀A,B,C: setoid1. ∀f: A → B → C. (∀a,a',b,b'. a=a' → b=b' → f a b = f a' b') →
  A ⇒_1 (unary_morphism1_setoid1 B C).
 #A; #B; #C; #f; #H; @ [ #x; @ (f x) ] #a; #a'; #Ha [##2: napply unary_morph1_eq1; #y]
 /2/.
nqed.

ndefinition composition1 ≝
 λo1,o2,o3:Type[1].λf:o2 → o3.λg: o1 → o2.λx.f (g x).
 
interpretation "function composition" 'compose f g = (composition ??? f g).
interpretation "function composition1" 'compose f g = (composition1 ??? f g).

ndefinition comp1_unary_morphisms: 
  ∀o1,o2,o3:setoid1.o2 ⇒_1 o3 → o1 ⇒_1 o2 → o1 ⇒_1 o3.
#o1; #o2; #o3; #f; #g; @ (f ∘ g);
 #a; #a'; #e; nnormalize; napply (.= †(†e)); napply #.
nqed.

unification hint 0 ≔ o1,o2,o3:setoid1,f:o2 ⇒_1 o3,g:o1 ⇒_1 o2;
   R ≟ (mk_unary_morphism1 ?? (composition1 ??? (fun11 ?? f) (fun11 ?? g))
        (prop11 ?? (comp1_unary_morphisms o1 o2 o3 f g)))
 (* -------------------------------------------------------------------- *) ⊢
       fun11 o1 o3 R ≡ composition1 ??? (fun11 ?? f) (fun11 ?? g).
                              
ndefinition comp1_binary_morphisms:
 ∀o1,o2,o3. (o2 ⇒_1 o3) ⇒_1 ((o1 ⇒_1 o2) ⇒_1 (o1 ⇒_1 o3)).
#o1; #o2; #o3; napply mk_binary_morphism1
 [ #f; #g; napply (comp1_unary_morphisms … f g) 
 | #a; #a'; #b; #b'; #ea; #eb; #x; #x'; #Hx; nnormalize; /3/ ]
nqed.
