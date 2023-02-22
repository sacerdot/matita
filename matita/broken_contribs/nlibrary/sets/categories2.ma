
include "sets/sets.ma".
include "sets/setoids2.ma".
include "sets/categories.ma".

(*
ndefinition binary_morph_setoid : setoid → setoid → setoid → setoid.
#S1; #S2; #T; @ (binary_morphism S1 S2 T); @;
##[ #f; #g; napply (∀x,y. f x y = g x y);
##| #f; #x; #y; napply #;
##| #f; #g; #H; #x; #y; napply ((H x y)^-1);
##| #f; #g; #h; #H1; #H2; #x; #y; napply (trans … (H1 …) (H2 …)); ##]
nqed.

ndefinition unary_morph_setoid : setoid → setoid → setoid.
#S1; #S2; @ (unary_morphism S1 S2); @;
##[ #f; #g; napply (∀x. f x = g x);
##| #f; #x; napply #;
##| #f; #g; #H; #x; napply ((H x)^-1);
##| #f; #g; #h; #H1; #H2; #x; napply (trans … (H1 …) (H2 …)); ##]
nqed.

nrecord category : Type[2] ≝
 { objs:> Type[1];
   arrows: objs → objs → setoid;
   id: ∀o:objs. arrows o o;
   comp: ∀o1,o2,o3. binary_morphism (arrows o1 o2) (arrows o2 o3) (arrows o1 o3);
   comp_assoc: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp o1 o3 o4 (comp o1 o2 o3 a12 a23) a34 = comp o1 o2 o4 a12 (comp o2 o3 o4 a23 a34);
   id_neutral_left: ∀o1,o2. ∀a: arrows o1 o2. comp ??? (id o1) a = a;
   id_neutral_right: ∀o1,o2. ∀a: arrows o1 o2. comp ??? a (id o2) = a
 }.
*)

notation "hvbox(A break ⇒ B)" right associative with precedence 55 for @{ 'arrows $A $B }.
interpretation "arrows1" 'arrows A B = (unary_morphism1 A B).
interpretation "arrows" 'arrows A B = (unary_morphism A B).

(*
notation > "𝐈𝐝 term 90 A" non associative with precedence 90 for @{ 'id $A }.
notation < "mpadded width -90% (𝐈) 𝐝 \sub term 90 A" non associative with precedence 90 for @{ 'id $A }.

interpretation "id" 'id A = (id ? A).

ndefinition SETOID : category.
@; 
##[ napply setoid;
##| napply unary_morph_setoid;
##| #o; @ (λx.x); #a; #b; #H; napply H;
##| #o1; #o2; #o3; @; 
    ##[ #f; #g; @(λx.g (f x)); #a; #b; #H; napply (.= (††H)); napply #;
    ##| #f; #g; #f'; #g'; #H1; #H2; nwhd; #x; napply (.= (H2 (f x)));
        napply (.= (†(H1 x))); napply #; ##]
##| #o1; #o2; #o3; #o4; #f; #g; #h; nwhd; #x; napply #;
##|##6,7: #o1; #o2; #f; nwhd; #x; napply #; ##]
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
    napply (∃f:T1 ⇒ T2.∃g:T2 ⇒ T1. (∀x.f (g x) = x) ∧ (∀y.g (f y) = y));
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
   prop01: ∀a,a'. eq ? a a' → eq1 ? (fun01 a) (fun01 a')
 }.
 
interpretation "prop01" 'prop1 c  = (prop01 ????? c).
*)
