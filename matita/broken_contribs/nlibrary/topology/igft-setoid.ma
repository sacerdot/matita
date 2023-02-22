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
   comp: ∀o1,o2,o3. unary_morphism (arrows o1 o2) (unary_morph_setoid (arrows o2 o3) (arrows o1 o3));
   comp_assoc: ∀o1,o2,o3,o4. ∀a12,a23,a34.
    comp o1 o3 o4 (comp o1 o2 o3 a12 a23) a34 = comp o1 o2 o4 a12 (comp o2 o3 o4 a23 a34);
   id_neutral_left: ∀o1,o2. ∀a: arrows o1 o2. comp ??? (id o1) a = a;
   id_neutral_right: ∀o1,o2. ∀a: arrows o1 o2. comp ??? a (id o2) = a
 }.

notation "hvbox(A break ⇒ B)" right associative with precedence 55 for @{ 'arrows $A $B }.
interpretation "arrows" 'arrows A B = (unary_morphism A B).

notation > "𝐈𝐝 term 90 A" non associative with precedence 90 for @{ 'id $A }.
notation < "mpadded width -90% (𝐈) 𝐝 \sub term 90 A" non associative with precedence 90 for @{ 'id $A }.

interpretation "id" 'id A = (id ? A).

ndefinition SETOID : category.
@; 
##[ napply setoid;
##| napply unary_morph_setoid;
##| #o; @ (λx.x); //
##| #o1; #o2; #o3; napply mk_binary_morphism [ #f; #g; @(λx.g (f x)) ]
    nnormalize; /3/
##| nnormalize; /4/
##|##6,7: nnormalize; /2/ ]
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

nrecord nAx : Type[1] ≝ { 
  nS:> setoid; 
  nI: unary_morphism01 nS TYPE;
  nD: ∀a:nS. unary_morphism01 (nI a) TYPE;
  nd: ∀a:nS. ∀i:nI a. unary_morphism (nD a i) nS
}.

notation "𝐃 \sub ( ❨a,\emsp i❩ )" non associative with precedence 70 for @{ 'D $a $i }.
notation "𝐝 \sub ( ❨a,\emsp i,\emsp j❩ )" non associative with precedence 70 for @{ 'd $a $i $j}.
notation "𝐈  \sub( ❨a❩ )" non associative with precedence 70 for @{ 'I $a }.

notation > "𝐈 term 90 a" non associative with precedence 70 for @{ 'I $a }.
notation > "𝐃 term 90 a term 90 i" non associative with precedence 70 for @{ 'D $a $i }.
notation > "𝐝 term 90 a term 90 i term 90 j" non associative with precedence 70 for @{ 'd $a $i $j}.

interpretation "D" 'D a i = (nD ? a i).
interpretation "d" 'd a i j = (nd ? a i j).
interpretation "new I" 'I a = (nI ? a).

ndefinition image ≝ λA:nAx.λa:A.λi. { x | ∃j:𝐃 a i. x = 𝐝 a i j }.
(*
nlemma elim_eq_TYPE : ∀A,B:setoid.∀P:CProp[1]. A=B → ((B ⇒ A) → P) → P.
#A; #B; #P; *; #f; *; #g; #_; #IH; napply IH; napply g;
nqed.

ninductive squash (A : Type[1]) : CProp[1] ≝
  | hide : A → squash A.     

nrecord unary_morphism_dep (A : setoid) (T:unary_morphism01 A TYPE) : Type[1] ≝ {
  fun_dep  : ∀a:A.(T a);
  prop_dep : ∀a,b:A. ∀H:a = b. 
    ? (prop01 … T … H) }.
##[##3: *; 
    
     (λf.hide ? (eq_rel ? (eq (T a)) (fun_dep a) (f (fun_dep b))))  
}.
##[##2: nletin lhs ≝ (fun_dep a:?); nletin rhs ≝ (fun_dep b:?);
        nletin patched_rhs ≝ (f rhs : ?);
        nlapply (lhs = patched_rhs);
        *)

(*
nlemma foo: ∀A:setoid.∀T:unary_morphism01 A TYPE.∀P:∀x:A.∀a:T x.CProp[0].
    ∀x,y:A.x=y → (∃a:T x.P ? a) = (∃a:T y.P ? a).
#A; #T; #P; #x; #y; #H; ncases (prop01 … T … H); #f; *; #g; *; #Hf; #Hg;
@; *; #e; #He;
##[ @(f e);   
*)

ndefinition image_is_ext : ∀A:nAx.∀a:A.∀i:𝐈 a.𝛀^A.
#A; #a; #i; @ (image … i); #x; #y; #H; @;
##[ *; #d; #Ex; @ d; napply (.= H^-1); nassumption;
##| *; #d; #Ex; @ d; napply (.= H); nassumption; ##]
nqed.

unification hint 0 ≔ A,a,i ;
       R ≟ (mk_ext_powerclass ? (image A a i) (ext_prop ? (image_is_ext A a i)))
 (* --------------------------------------------------------------- *) ⊢
      ext_carr A R ≡ (image A a i).

notation > "𝐈𝐦  [𝐝 term 90 a term 90 i]" non associative with precedence 70 for @{ 'Im $a $i }.
notation < "mpadded width -90% (𝐈) 𝐦  [𝐝 \sub ( ❨a,\emsp i❩ )]" non associative with precedence 70 for @{ 'Im $a $i }.

interpretation "image" 'Im a i = (image ? a i).

ninductive Ord (A : nAx) : Type[0] ≝ 
 | oO : Ord A
 | oS : Ord A → Ord A
 | oL : ∀a:A.∀i.∀f:𝐃 a i → Ord A. Ord A.

notation "0" non associative with precedence 90 for @{ 'oO }.
notation "Λ term 90 f" non associative with precedence 55 for @{ 'oL $f }.
notation "x+1" non associative with precedence 55 for @{'oS $x }.

interpretation "ordinals Zero" 'oO = (oO ?).
interpretation "ordinals Lambda" 'oL f = (oL ? ? ? f).
interpretation "ordinals Succ" 'oS x = (oS ? x).

(* manca russell *)
nlet rec famU (A : nAx) (U : 𝛀^A) (x : Ord A) on x : 𝛀^A ≝ 
  match x with
  [ oO ⇒ mk_ext_powerclass A U ?
  | oS y ⇒ let Un ≝ famU A U y in mk_ext_powerclass A (Un ∪ { x | ∃i.𝐈𝐦[𝐝 x i] ⊆ Un}) ? 
  | oL a i f ⇒ mk_ext_powerclass A { x | ∃j.x ∈ famU A U (f j) } ? ].
##[ #x; #y; #H; alias symbol "trans" = "trans1".
    alias symbol "prop2" = "prop21".
    napply (.= (H‡#)); napply #;
##| #x; #y; #H; @; *;
    ##[##1,3: #E; @1; ##[ napply (. (ext_prop A Un … H^-1)); ##| napply (. (ext_prop A Un … H)); ##]
              nassumption;
    ##|##*: *; #i; #H1; @2; 
            ##[ nlapply (†H); ##[ napply (nI A); ##| ##skip ##]
                #W; ncases W; #f; *; #g; *; #Hf; #Hg;
                @ (f i); #a; #Ha; napply H1;
                ncut (𝐈𝐦[𝐝 y (f i)] = 𝐈𝐦[𝐝 x i]); 
                
                ##[##2: #E; napply (. (#‡E^-1)); napply Ha; ##]
                        
                @; #w; #Hw; nwhd;
                ncut (𝐈𝐦[𝐝 y (f i)] = 𝐈𝐦[𝐝 x i]);                    
                  
(*    
  
notation < "term 90 U \sub (term 90 x)" non associative with precedence 55 for @{ 'famU $U $x }.
notation > "U ⎽ term 90 x" non associative with precedence 55 for @{ 'famU $U $x }.

interpretation "famU" 'famU U x = (famU ? U x).

(*D

We attach as the input notation for U_x the similar `U⎽x` where underscore,
that is a character valid for identifier names, has been replaced by `⎽` that is
not. The symbol `⎽` can act as a separator, and can be typed as an alternative
for `_` (i.e. pressing ALT-L after `_`). 

The notion ◃(U) has to be defined as the subset of of y 
belonging to U_x for some x. Moreover, we have to define the notion
of cover between sets again, since the one defined at the beginning
of the tutorial works only for the old axiom set definition.

D*)
  
ndefinition ord_coverage : ∀A:nAx.∀U:Ω^A.Ω^A ≝ λA,U.{ y | ∃x:Ord A. y ∈ famU ? U x }.

ndefinition ord_cover_set ≝ λc:∀A:nAx.Ω^A → Ω^A.λA,C,U.
  ∀y.y ∈ C → y ∈ c A U.

interpretation "coverage new cover" 'coverage U = (ord_coverage ? U).
interpretation "new covers set" 'covers a U = (ord_cover_set ord_coverage ? a U).
interpretation "new covers" 'covers a U = (mem ? (ord_coverage ? U) a).

(*D

Before proving that this cover relation validates the reflexivity and infinity
rules, we prove this little technical lemma that is used in the proof for the 
infinity rule.

D*)

nlemma ord_subset:
  ∀A:nAx.∀a:A.∀i,f,U.∀j:𝐃 a i.U⎽(f j) ⊆ U⎽(Λ f).
#A; #a; #i; #f; #U; #j; #b; #bUf; @ j; nassumption;
nqed.

(*D

The proof of infinity uses the following form of the Axiom of choice,
that cannot be prove inside Matita, since the existential quantifier
lives in the sort of predicative propositions while the sigma in the conclusion
lives in the sort of data types, and thus the former cannot be eliminated
to provide the second.

D*)

naxiom AC : ∀A,a,i,U.
  (∀j:𝐃 a i.∃x:Ord A.𝐝 a i j ∈ U⎽x) → (Σf.∀j:𝐃 a i.𝐝 a i j ∈ U⎽(f j)).

(*D

In the proof of infinity, we have to rewrite under the ∈ predicate.
It is clearly possible to show that U_x is an extensional set:

> a=b → a ∈ U_x → b ∈ U_x

Anyway this proof in non trivial induction over x, that requires 𝐈 and 𝐃 to be
declared as morphisms. This poses to problem, but goes out of the scope of the 
tutorial and we thus assume it.

D*)

naxiom setoidification :
  ∀A:nAx.∀a,b:A.∀x.∀U.a=b → b ∈ U⎽x → a ∈ U⎽x.

(*D

The reflexivity proof is trivial, it is enough to provide the ordinal 0
as a witness, then ◃(U) reduces to U by definition, hence the conclusion.

D*)
ntheorem new_coverage_reflexive:
  ∀A:nAx.∀U:Ω^A.∀a. a ∈ U → a ◃ U.
#A; #U; #a; #H; @ (0); napply H;
nqed.

(*D

We now proceed with the proof of the infinity rule.

D*)

alias symbol "covers" = "new covers set".
alias symbol "covers" = "new covers".
alias symbol "covers" = "new covers set".
alias symbol "covers" = "new covers".
alias symbol "covers" = "new covers set".
alias symbol "covers" = "new covers".
ntheorem new_coverage_infinity:
  ∀A:nAx.∀U:Ω^A.∀a:A. (∃i:𝐈 a. 𝐈𝐦[𝐝 a i] ◃ U) → a ◃ U.
#A; #U; #a;                                   (** screenshot "n-cov-inf-1". *)  
*; #i; #H; nnormalize in H;                   (** screenshot "n-cov-inf-2". *)
ncut (∀y:𝐃 a i.∃x:Ord A.𝐝 a i y ∈ U⎽x); ##[    (** screenshot "n-cov-inf-3". *)
  #z; napply H; @ z; napply #; ##] #H';       (** screenshot "n-cov-inf-4". *)
ncases (AC … H'); #f; #Hf;                    (** screenshot "n-cov-inf-5". *)
ncut (∀j.𝐝 a i j ∈ U⎽(Λ f));
  ##[ #j; napply (ord_subset … f … (Hf j));##] #Hf';(** screenshot "n-cov-inf-6". *)
@ (Λ f+1);                                    (** screenshot "n-cov-inf-7". *)
@2;                                           (** screenshot "n-cov-inf-8". *) 
@i; #x; *; #d; #Hd;                           (** screenshot "n-cov-inf-9". *)  
napply (setoidification … Hd); napply Hf';
nqed.

(*D
D[n-cov-inf-1]
We eliminate the existential, obtaining an `i` and a proof that the 
image of d(a,i) is covered by U. The `nnormalize` tactic computes the normal
form of `H`, thus expands the definition of cover between sets.

D[n-cov-inf-2]
The paper proof considers `H` implicitly substitutes the equation assumed
by `H` in its conclusion. In Matita this step is not completely trivia.
We thus assert (`ncut`) the nicer form of `H`.

D[n-cov-inf-3]
After introducing `z`, `H` can be applied (choosing `𝐝 a i z` as `y`). 
What is the left to prove is that `∃j: 𝐃 a j. 𝐝 a i z = 𝐝 a i j`, that 
becomes trivial is `j` is chosen to be `z`. In the command `napply #`,
the `#` is a standard notation for the reflexivity property of the equality. 

D[n-cov-inf-4]
Under `H'` the axiom of choice `AC` can be eliminated, obtaining the `f` and 
its property.

D[n-cov-inf-5]
The paper proof does now a forward reasoning step, deriving (by the ord_subset 
lemma we proved above) `Hf'` i.e. 𝐝 a i j ∈ U⎽(Λf).

D[n-cov-inf-6]
To prove that `a◃U` we have to exhibit the ordinal x such that `a ∈ U⎽x`.

D[n-cov-inf-7]
The definition of `U⎽(…+1)` expands to the union of two sets, and proving
that `a ∈ X ∪ Y` is defined as proving that `a` is in `X` or `Y`. Applying
the second constructor `@2;` of the disjunction, we are left to prove that `a` 
belongs to the right hand side.

D[n-cov-inf-8]
We thus provide `i`, introduce the element being in the image and we are
left to prove that it belongs to `U_(Λf)`. In the meanwhile, since belonging 
to the image means that there exists an object in the domain… we eliminate the
existential, obtaining `d` (of type `𝐃 a i`) and the equation defining `x`.  

D[n-cov-inf-9]
We just need to use the equational definition of `x` to obtain a conclusion
that can be proved with `Hf'`. We assumed that `U_x` is extensional for
every `x`, thus we are allowed to use `Hd` and close the proof.

D*)

(*D

The next proof is that ◃(U) is mininal. The hardest part of the proof
it to prepare the goal for the induction. The desiderata is to prove
`U⎽o ⊆ V` by induction on `o`, but the conclusion of the lemma is,
unfolding all definitions:

> ∀x. x ∈ { y | ∃o:Ord A.y ∈ U⎽o } → x ∈ V

D*)

nlemma new_coverage_min :  
  ∀A:nAx.∀U:Ω^A.∀V.U ⊆ V → (∀a:A.∀i.𝐈𝐦[𝐝 a i] ⊆ V → a ∈ V) → ◃U ⊆ V.
#A; #U; #V; #HUV; #Im;#b;                       (** screenshot "n-cov-min-2". *)
*; #o;                                          (** screenshot "n-cov-min-3". *)
ngeneralize in match b; nchange with (U⎽o ⊆ V); (** screenshot "n-cov-min-4". *)
nelim o;                                        (** screenshot "n-cov-min-5". *) 
##[ #b; #bU0; napply HUV; napply bU0;
##| #p; #IH; napply subseteq_union_l; ##[ nassumption; ##]
    #x; *; #i; #H; napply (Im ? i); napply (subseteq_trans … IH); napply H;
##| #a; #i; #f; #IH; #x; *; #d; napply IH; ##]
nqed.

(*D
D[n-cov-min-2]
After all the introductions, event the element hidden in the ⊆ definition,
we have to eliminate the existential quantifier, obtaining the ordinal `o`

D[n-cov-min-3]
What is left is almost right, but the element `b` is already in the
context. We thus generalize every occurrence of `b` in 
the current goal, obtaining `∀c.c ∈ U⎽o → c ∈ V` that is `U⎽o ⊆ V`.

D[n-cov-min-4]
We then proceed by induction on `o` obtaining the following goals

D[n-cov-min-5]
All of them can be proved using simple set theoretic arguments,
the induction hypothesis and the assumption `Im`.

D*)


(*D

bla bla

D*)

nlet rec famF (A: nAx) (F : Ω^A) (x : Ord A) on x : Ω^A ≝ 
  match x with
  [ oO ⇒ F
  | oS o ⇒ let Fo ≝ famF A F o in Fo ∩ { x | ∀i:𝐈 x.∃j:𝐃 x i.𝐝 x i j ∈ Fo } 
  | oL a i f ⇒ { x | ∀j:𝐃 a i.x ∈ famF A F (f j) }
  ].

interpretation "famF" 'famU U x = (famF ? U x).

ndefinition ord_fished : ∀A:nAx.∀F:Ω^A.Ω^A ≝ λA,F.{ y | ∀x:Ord A. y ∈ F⎽x }.

interpretation "fished new fish" 'fished U = (ord_fished ? U).
interpretation "new fish" 'fish a U = (mem ? (ord_fished ? U) a).

(*D

The proof of compatibility uses this little result, that we 
factored out. 

D*)
nlemma co_ord_subset:
 ∀A:nAx.∀F:Ω^A.∀a,i.∀f:𝐃 a i → Ord A.∀j. F⎽(Λ f) ⊆ F⎽(f j).
#A; #F; #a; #i; #f; #j; #x; #H; napply H;
nqed.

(*D

We assume the dual of the axiom of choice, as in the paper proof.

D*)
naxiom AC_dual : 
  ∀A:nAx.∀a:A.∀i,F. (∀f:𝐃 a i → Ord A.∃x:𝐃 a i.𝐝 a i x ∈ F⎽(f x)) → ∃j:𝐃 a i.∀x:Ord A.𝐝 a i j ∈ F⎽x.

(*D

Proving the anti-reflexivity property is simce, since the
assumption `a ⋉ F` states that for every ordinal `x` (and thus also 0)
`a ∈ F⎽x`. If `x` is choosen to be `0`, we obtain the thesis.

D*)
ntheorem new_fish_antirefl:
 ∀A:nAx.∀F:Ω^A.∀a. a ⋉ F → a ∈ F.
#A; #F; #a; #H; nlapply (H 0); #aFo; napply aFo;
nqed.

(*D

bar

D*)
ntheorem new_fish_compatible: 
 ∀A:nAx.∀F:Ω^A.∀a. a ⋉ F → ∀i:𝐈 a.∃j:𝐃 a i.𝐝 a i j ⋉ F.
#A; #F; #a; #aF; #i; nnormalize;               (** screenshot "n-f-compat-1". *)
napply AC_dual; #f;                            (** screenshot "n-f-compat-2". *)
nlapply (aF (Λf+1)); #aLf;                     (** screenshot "n-f-compat-3". *)
nchange in aLf with 
  (a ∈ F⎽(Λ f) ∧ ∀i:𝐈 a.∃j:𝐃 a i.𝐝 a i j ∈ F⎽(Λ f)); (** screenshot "n-f-compat-4". *)
ncut (∃j:𝐃 a i.𝐝 a i j ∈ F⎽(f j));##[
  ncases aLf; #_; #H; nlapply (H i);               (** screenshot "n-f-compat-5". *) 
  *; #j; #Hj; @j; napply Hj;##] #aLf';             (** screenshot "n-f-compat-6". *)
napply aLf';
nqed.

(*D
D[n-f-compat-1]
D[n-f-compat-2]
D[n-f-compat-3]
D[n-f-compat-4]
D[n-f-compat-5]
D[n-f-compat-6]

D*)

(*D

The proof that `⋉(F)` is maximal is exactly the dual one of the
minimality of `◃(U)`. Thus the main problem is to obtain `G ⊆ F⎽o`
before doing the induction over `o`.

D*)
ntheorem max_new_fished: 
  ∀A:nAx.∀G:ext_powerclass_setoid A.∀F:Ω^A.G ⊆ F → (∀a.a ∈ G → ∀i.𝐈𝐦[𝐝 a i] ≬ G) → G ⊆ ⋉F.
#A; #G; #F; #GF; #H; #b; #HbG; #o; 
ngeneralize in match HbG; ngeneralize in match b;
nchange with (G ⊆ F⎽o);
nelim o;
##[ napply GF;
##| #p; #IH; napply (subseteq_intersection_r … IH);
    #x; #Hx; #i; ncases (H … Hx i); #c; *; *; #d; #Ed; #cG;
    @d; napply IH;
    alias symbol "prop2" = "prop21".
napply (. Ed^-1‡#); napply cG;    
##| #a; #i; #f; #Hf; nchange with (G ⊆ { y | ∀x. y ∈ F⎽(f x) }); 
    #b; #Hb; #d; napply (Hf d); napply Hb;
##]
nqed.


(*D
<div id="appendix" class="anchor"></div>
Appendix: tactics explanation
-----------------------------

In this appendix we try to give a description of tactics
in terms of sequent calculus rules annotated with proofs.
The `:` separator has to be read as _is a proof of_, in the spirit
of the Curry-Howard isomorphism.

                  Γ ⊢  f  :  A1 → … → An → B    Γ ⊢ ?1 : A1 … ?n  :  An 
    napply f;    ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                           Γ ⊢ (f ?1 … ?n )  :  B
 
                   Γ ⊢  ?  :  F → B       Γ ⊢ f  :  F 
    nlapply f;    ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                             Γ ⊢ (? f)  :  B


                 Γ; x : T  ⊢ ?  :  P(x) 
    #x;      ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                Γ ⊢ λx:T.?  :  ∀x:T.P(x)

                       
                       Γ ⊢ ?_i  :  args_i → P(k_i args_i)          
    ncases x;   ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                Γ ⊢ match x with [ k1 args1 ⇒ ?_1 | … | kn argsn ⇒ ?_n ]  :  P(x)                    


                      Γ ⊢ ?i  :  ∀t. P(t) → P(k_i … t …)          
    nelim x;   ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                   Γ ⊢ (T_rect_CProp0 ?_1 … ?_n)  :  P(x)                    

Where `T_rect_CProp0` is the induction principle for the 
inductive type `T`.

                          Γ ⊢ ?  :  Q     Q ≡ P          
    nchange with Q;   ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                          Γ ⊢ ?  :  P                    

Where the equivalence relation between types `≡` keeps into account
β-reduction, δ-reduction (definition unfolding), ζ-reduction (local
definition unfolding), ι-reduction (pattern matching simplification),
μ-reduction (recursive function computation) and ν-reduction (co-fixpoint
computation).


                               Γ; H : Q; Δ ⊢ ?  :  G     Q ≡ P          
    nchange in H with Q; ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                               Γ; H : P; Δ ⊢ ?  :  G                    



                    Γ ⊢ ?_2  :  T → G    Γ ⊢ ?_1  :  T
    ncut T;   ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                               Γ ⊢ (?_2 ?_1)  :  G                    


                                Γ ⊢ ?  :  ∀x.P(x)
    ngeneralize in match t; ⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼⎼
                                Γ ⊢ (? t)  :  P(t)
                                
D*)


(*D

[1]: http://upsilon.cc/~zack/research/publications/notation.pdf 

D*)
*)
