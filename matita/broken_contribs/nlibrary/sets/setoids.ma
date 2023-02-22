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

include "logic/connectives.ma".
include "properties/relations.ma".
include "hints_declaration.ma".

nrecord setoid : Type[1] ≝ { 
  carr:> Type[0];
  eq0: equivalence_relation carr
}.

(* activate non uniform coercions on: Type → setoid *)
unification hint 0 ≔ R : setoid;
   MR ≟ carr R, 
   lock ≟ mk_lock1 Type[0] MR setoid R 
(* ---------------------------------------- *) ⊢ 
   setoid ≡ force1 ? MR lock.

notation < "[\setoid\ensp\of term 19 x]" non associative with precedence 90 for @{'mk_setoid $x}.
interpretation "mk_setoid" 'mk_setoid x = (mk_setoid x ?).

interpretation "setoid eq" 'eq t x y = (eq_rel ? (eq0 t) x y).
(* single = is for the abstract equality of setoids, == is for concrete 
   equalities (that may be lifted to the setoid level when needed *)
notation < "hvbox(a break mpadded width -50% (=)= b)" non associative with precedence 45 for @{ 'eq_low $a $b }.
notation > "a == b" non associative with precedence 45 for @{ 'eq_low $a $b }.

notation > "hvbox(a break =_0 b)" non associative with precedence 45
for @{ eq_rel ? (eq0 ?) $a $b }.

interpretation "setoid symmetry" 'invert r = (sym ???? r).
notation ".= r" with precedence 55 for @{'trans $r}.
interpretation "trans" 'trans r = (trans ????? r).
notation > ".=_0 r" with precedence 55 for @{'trans_x0 $r}.
interpretation "trans_x0" 'trans_x0 r = (trans ????? r).

nrecord unary_morphism (A,B: setoid) : Type[0] ≝ { 
  fun1:1> A → B;
  prop1: ∀a,a'. a = a' → fun1 a = fun1 a'
}.

notation > "B ⇒_0 C" right associative with precedence 72 for @{'umorph0 $B $C}.
notation "hvbox(B break ⇒\sub 0 C)" right associative with precedence 72 for @{'umorph0 $B $C}.
interpretation "unary morphism 0" 'umorph0 A B = (unary_morphism A B).

notation "† c" with precedence 90 for @{'prop1 $c }.
notation "l ‡ r" with precedence 90 for @{'prop2 $l $r }.
notation "#" with precedence 90 for @{'refl}.
interpretation "prop1" 'prop1 c  = (prop1 ????? c).
interpretation "refl" 'refl = (refl ???).
notation "┼_0 c" with precedence 89 for @{'prop1_x0 $c }.
notation "l ╪_0 r" with precedence 89 for @{'prop2_x0 $l $r }.
interpretation "prop1_x0" 'prop1_x0 c  = (prop1 ????? c).

ndefinition unary_morph_setoid : setoid → setoid → setoid.
#S1; #S2; @ (S1 ⇒_0 S2); @;
##[ #f; #g; napply (∀x,x'. x=x' → f x = g x');
##| #f; #x; #x'; #Hx; napply (.= †Hx); napply #;
##| #f; #g; #H; #x; #x'; #Hx; napply ((H … Hx^-1)^-1);
##| #f; #g; #h; #H1; #H2; #x; #x'; #Hx; napply (trans … (H1 …) (H2 …)); //; ##]
nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ o1,o2 ; 
     X ≟ unary_morph_setoid o1 o2
  (* ----------------------------- *) ⊢ 
     carr X ≡ o1 ⇒_0 o2.

interpretation "prop2" 'prop2 l r = (prop1 ? (unary_morph_setoid ??) ? ?? l ?? r).
interpretation "prop2_x0" 'prop2_x0 l r = (prop1 ? (unary_morph_setoid ??) ? ?? l ?? r).

nlemma unary_morph_eq: ∀A,B.∀f,g:A ⇒_0 B. (∀x. f x = g x) → f = g.
#A B f g H x1 x2 E; napply (.= †E); napply H; nqed.

nlemma mk_binary_morphism:
 ∀A,B,C: setoid. ∀f: A → B → C. (∀a,a',b,b'. a=a' → b=b' → f a b = f a' b') →
  A ⇒_0 (unary_morph_setoid B C).
 #A; #B; #C; #f; #H; @; ##[ #x; @ (f x) ] #a; #a'; #Ha [##2: napply unary_morph_eq; #y]
 /2/.
nqed.

ndefinition composition ≝
 λo1,o2,o3:Type[0].λf:o2 → o3.λg: o1 → o2.λx.f (g x).
 
interpretation "function composition" 'compose f g = (composition ??? f g).

ndefinition comp_unary_morphisms:
 ∀o1,o2,o3:setoid.o2 ⇒_0 o3 → o1 ⇒_0 o2 → o1 ⇒_0  o3.
#o1; #o2; #o3; #f; #g; @ (f ∘ g);
 #a; #a'; #e; nnormalize; napply (.= †(†e)); napply #.
nqed.

unification hint 0 ≔ o1,o2,o3:setoid,f:o2 ⇒_0 o3,g:o1 ⇒_0 o2;
   R ≟ mk_unary_morphism o1 o3 
        (composition ??? (fun1 o2 o3 f) (fun1 o1 o2 g))
        (prop1 o1 o3 (comp_unary_morphisms o1 o2 o3 f g))
 (* -------------------------------------------------------------------- *) ⊢
    fun1 o1 o3 R ≡ composition ??? (fun1 o2 o3 f) (fun1 o1 o2 g).

ndefinition comp_binary_morphisms: 
  ∀o1,o2,o3.(o2 ⇒_0 o3) ⇒_0 ((o1 ⇒_0 o2) ⇒_0 (o1 ⇒_0 o3)).
#o1; #o2; #o3; napply mk_binary_morphism
 [ #f; #g; napply (comp_unary_morphisms ??? f g) 
         (* CSC: why not ∘? 
            GARES: because the coercion to FunClass is not triggered if there
                   are no "extra" arguments. We could fix that in the refiner
         *)
 | #a; #a'; #b; #b'; #ea; #eb; #x; #x'; #Hx; nnormalize; /3/ ]
nqed.
