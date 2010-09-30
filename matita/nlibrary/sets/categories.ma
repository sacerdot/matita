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


include "sets/sets.ma".

nrecord category : Type[2] ≝
 { objs:> Type[1];
   arrows: objs → objs → setoid;
   id: ∀o:objs. arrows o o;
   comp: ∀o1,o2,o3. unary_morphism (arrows o2 o3) (unary_morph_setoid (arrows o1 o2) (arrows o1 o3));
   comp_assoc: ∀o1,o2,o3,o4. ∀a34,a23,a12.
    comp o1 o3 o4 a34 (comp o1 o2 o3 a23 a12) = comp o1 o2 o4 (comp o2 o3 o4 a34 a23) a12;
   id_neutral_left: ∀o1,o2. ∀a: arrows o1 o2. comp ??? (id o2) a = a;
   id_neutral_right: ∀o1,o2. ∀a: arrows o1 o2. comp ??? a (id o1) = a
 }.

notation > "𝐈𝐝 term 90 A" non associative with precedence 90 for @{ 'id $A }.
notation < "mpadded width -90% (𝐈) 𝐝 \sub term 90 A" non associative with precedence 90 for @{ 'id $A }.

interpretation "id" 'id A = (id ? A).

ndefinition SETOID : category.
@; 
##[ napply setoid;
##| napply unary_morph_setoid;
##| #o; @ (λx.x); #a; #b; #H; napply H;
##| napply comp_binary_morphisms; (*CSC: why not ∘?*)
##| #o1; #o2; #o3; #o4; #f; #g; #h; #x; #x'; #Hx; nnormalize; napply (†(†(†Hx)))
##|##6,7: #o1; #o2; #f; #x; #x'; #Hx; nnormalize; napply (†Hx) ]
nqed.

unification hint 0 ≔ ;
   R ≟ (mk_category setoid unary_morph_setoid (id SETOID) (comp SETOID)
          (comp_assoc SETOID) (id_neutral_left SETOID)
          (id_neutral_right SETOID))
 (* -------------------------------------------------------------------- *) ⊢
                              objs R ≡ setoid.
                              
 unification hint 0 ≔ x,y ;
   R ≟ (mk_category setoid unary_morph_setoid (id SETOID) (comp SETOID)
          (comp_assoc SETOID) (id_neutral_left SETOID)
          (id_neutral_right SETOID))
 (* -------------------------------------------------------------------- *) ⊢
                  arrows R x y ≡ unary_morph_setoid x y. 
                  
unification hint 0 ≔ A,B ;               
                  T ≟ (unary_morph_setoid A B)
           (* ----------------------------------- *) ⊢              
                  unary_morphism A B ≡ carr T. 
                
                
ndefinition TYPE : setoid1.
@ setoid; @; 
##[ #T1; #T2; 
    alias symbol "eq" = "setoid eq".
    napply (∃f:T1 ⇒_0 T2.∃g:T2 ⇒_0 T1. (∀x.f (g x) = x) ∧ (∀y.g (f y) = y));
##| #A; @ (𝐈𝐝 A); @ (𝐈𝐝 A); @; #x; napply #;
##| #A; #B; *; #f; *; #g; *; #Hfg; #Hgf; @g; @f; @; nassumption; 
##| #A; #B; #C; *; #f; *; #f'; *; #Hf; #Hf'; *; #g; *; #g'; *; #Hg; #Hg'; 
    @; ##[ @(λx.g (f x)); #a; #b; #H; napply (.= (††H)); napply #;
       ##| @; ##[ @(λx.f'(g' x)); #a; #b; #H; napply (.= (††H)); napply #; ##]
    @; #x;
    ##[ napply (.= (†(Hf …))); napply Hg;
    ##| napply (.= (†(Hg' …))); napply Hf'; ##] ##] 
nqed.

unification hint 0 ≔ ;
          R ≟ (mk_setoid1 setoid (eq1 TYPE))
  (* -------------------------------------------- *) ⊢
                 carr1 R ≡ setoid.
   
nrecord unary_morphism01 (A : setoid) (B: setoid1) : Type[1] ≝
 { fun01:1> A → B;
   prop01: ∀a,a'. eq0 ? a a' → eq1 ? (fun01 a) (fun01 a')
 }.
 
interpretation "prop01" 'prop1 c  = (prop01 ????? c).
