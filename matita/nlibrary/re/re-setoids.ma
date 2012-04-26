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

include "datatypes/pairs-setoids.ma".
include "datatypes/bool-setoids.ma".
include "datatypes/list-setoids.ma".
include "sets/sets.ma".

(*
ninductive Admit : CProp[0] ≝ .
naxiom admit : Admit.
*)

(* XXX move somewere else *)
ndefinition if': ∀A,B:CPROP. A = B → A → B.
#A B; *; /2/. nqed.

ncoercion if : ∀A,B:CPROP. ∀p:A = B. A → B ≝ if' on _p : eq_rel1 ? (eq1 CPROP) ?? to ∀_:?.?.

ndefinition ifs': ∀S.∀A,B:Ω^S. A = B → ∀x. x ∈ A → x ∈ B.
#S A B; *; /2/. nqed.

ncoercion ifs : ∀S.∀A,B:Ω^S. ∀p:A = B.∀x. x ∈ A → x ∈ B ≝ ifs' on _p : eq_rel1 ? (eq1 (powerclass_setoid ?))?? to ∀_:?.?.

(* XXX move to list-setoids-theory.ma *)

ntheorem append_nil: ∀A:setoid.∀l:list A.l @ [] = l.
#A;#l;nelim l;//; #a;#l1;#IH;nnormalize;/2/;nqed.

ndefinition associative ≝ λA:setoid.λf:A → A → A.∀x,y,z.f x (f y z) = f (f x y) z. 

ntheorem associative_append: ∀A:setoid.associative (list A) (append A).
#A;#x;#y;#z;nelim x[ napply (refl ???) |#a;#x1;#H;nnormalize;/2/]nqed.

(* end move to list *)


(* XXX to undestand what I want inside Alpha 
   the eqb part should be split away, but when available it should be
   possible to obtain a leibnitz equality on lemmas proved on setoids
*)
interpretation "iff" 'iff a b = (iff a b).  

ninductive eq (A:Type[0]) (x:A) : A → CProp[0] ≝ erefl: eq A x x.

nlemma eq_rect_Type0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type[0]. P a (erefl A a) → P x p.
 #A; #a; #x; #p; ncases p; #P; #H; nassumption.
nqed.

nlemma eq_rect_Type0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[0]. P a (erefl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; napply (eq_rect_Type0_r' ??? p0); nassumption.
nqed.

nlemma eq_rect_CProp0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (erefl A a) → P x p.
 #A; #a; #x; #p; ncases p; #P; #H; nassumption.
nqed.

nlemma eq_rect_CProp0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (erefl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; napply (eq_rect_CProp0_r' ??? p0); nassumption.
nqed.

nrecord Alpha : Type[1] ≝ { 
   acarr :> setoid;
   eqb: acarr → acarr → bool; 
   eqb_true: ∀x,y. (eqb x y = true) = (x = y)
}.
 
interpretation "eqb" 'eq_low a b = (eqb ? a b).
(* end alpha *)

(* re *)
ninductive re (S: Type[0]) : Type[0] ≝
   z: re S
 | e: re S
 | s: S → re S
 | c: re S → re S → re S
 | o: re S → re S → re S
 | k: re S → re S.
 
notation < "a \sup ⋇" non associative with precedence 90 for @{ 'pk $a}.
notation > "a ^ *" non associative with precedence 75 for @{ 'pk $a}.
interpretation "star" 'pk a = (k ? a).
interpretation "or" 'plus a b = (o ? a b).
           
notation "a · b" non associative with precedence 65 for @{ 'pc $a $b}.
interpretation "cat" 'pc a b = (c ? a b).

(* to get rid of \middot *)
ncoercion c  : ∀S.∀p:re S.  re S →  re S   ≝ c  on _p : re ?  to ∀_:?.?.

notation < "a" non associative with precedence 90 for @{ 'ps $a}.
notation > "` term 90 a" non associative with precedence 90 for @{ 'ps $a}.
interpretation "atom" 'ps a = (s ? a).

notation "ϵ" non associative with precedence 90 for @{ 'epsilon }.
interpretation "epsilon" 'epsilon = (e ?).

notation "0" non associative with precedence 90 for @{ 'empty_r }.
interpretation "empty" 'empty_r = (z ?).

notation > "'lang' S" non associative with precedence 90 for @{ Ω^(list $S) }.
notation > "'Elang' S" non associative with precedence 90 for @{ 𝛀^(LIST $S) }.
 
(* setoid support for re *)
 
nlet rec eq_re (S:Alpha) (a,b : re S) on a : CProp[0] ≝ 
  match a with
  [ z ⇒ match b with [ z ⇒ True | _ ⇒ False]
  | e ⇒ match b with [ e ⇒ True | _ ⇒ False]
  | s x ⇒ match b with [ s y ⇒ x = y | _ ⇒ False]
  | c r1 r2 ⇒ match b with [ c s1 s2 ⇒ eq_re ? r1 s1 ∧ eq_re ? r2 s2 | _ ⇒ False]
  | o r1 r2 ⇒ match b with [ o s1 s2  ⇒ eq_re ? r1 s1 ∧ eq_re ? r2 s2 | _ ⇒ False] 
  | k r1 ⇒ match b with [ k r2 ⇒ eq_re ? r1 r2 | _ ⇒ False]].
  
interpretation "eq_re" 'eq_low a b = (eq_re ? a b).

ndefinition RE : Alpha → setoid.
#A; @(re A); @(eq_re A);
##[ #p; nelim p; /2/;
##| #p1; nelim p1; ##[##1,2: #p2; ncases p2; /2/;
    ##|##2,3: #x p2; ncases p2; /2/;
    ##|##4,5: #e1 e2 H1 H2 p2; ncases p2; /3/; #e3 e4; *; #; @; /2/;
    ##|#r H p2; ncases p2; /2/;##]
##| #p1; nelim p1;
    ##[ ##1,2: #y z; ncases y; ncases z; //; nnormalize; #; ncases (?:False); //;
    ##| ##3: #a; #y z; ncases y; ncases z; /2/; nnormalize; #; ncases (?:False); //;
    ##| ##4,5: #r1 r2 H1 H2 y z; ncases y; ncases z; //; nnormalize;
        ##[##1,3,4,5,6,8: #; ncases (?:False); //;##]
        #r1 r2 r3 r4; nnormalize; *; #H1 H2; *; #H3 H4; /3/;
    ##| #r H y z; ncases y; ncases z; //; nnormalize; ##[##1,2,3: #; ncases (?:False); //]
        #r2 r3; /3/; ##]##]
nqed.

unification hint 0 ≔ A : Alpha;
  S ≟ acarr A,
  T ≟ carr S,
  P1 ≟ refl ? (eq0 (RE A)),
  P2 ≟ sym ? (eq0 (RE A)),
  P3 ≟ trans ? (eq0 (RE A)),
  X ≟ mk_setoid (re T) (mk_equivalence_relation ? (eq_re A) P1 P2 P3)
(*-----------------------------------------------------------------------*) ⊢
     carr X ≡ re T.

unification hint 0 ≔ A:Alpha, a,b:re (carr (acarr A));
   R ≟ eq0 (RE A),
   L ≟ re (carr (acarr A))
(* -------------------------------------------- *) ⊢
   eq_re A a b ≡ eq_rel L R a b.

nlemma c_is_morph : ∀A:Alpha.(re A) ⇒_0 (re A) ⇒_0 (re A).
#A; napply (mk_binary_morphism … (λs1,s2:re A. s1 · s2));
#a; nelim a; 
##[##1,2: #a' b b'; ncases a'; nnormalize; /2/ by conj;
##|#x a' b b'; ncases a'; /2/ by conj;
##|##4,5: #r1 r2 IH1 IH2 a'; ncases a'; nnormalize; /2/ by conj;
##|#r IH a'; ncases a'; nnormalize; /2/ by conj; ##]
nqed.

(* XXX This is the good format for hints about morphisms, fix the others *)
alias symbol "hint_decl" (instance 1) = "hint_decl_Type0".
unification hint 0 ≔ S:Alpha, A,B:re (carr (acarr S));
    SS ≟ carr (acarr S),
    MM ≟ mk_unary_morphism ?? (λA.
           mk_unary_morphism ?? 
             (λB.A · B) (prop1 ?? (fun1 ?? (c_is_morph S) A)))
           (prop1 ?? (c_is_morph S)),
    T ≟ RE S
(*--------------------------------------------------------------------------*) ⊢
   fun1 T T (fun1 T (unary_morph_setoid T T) MM A) B ≡ c SS A B.

nlemma o_is_morph : ∀A:Alpha.(re A) ⇒_0 (re A) ⇒_0 (re A).
#A; napply (mk_binary_morphism … (λs1,s2:re A. s1 + s2));
#a; nelim a; 
##[##1,2: #a' b b'; ncases a'; nnormalize; /2/ by conj;
##|#x a' b b'; ncases a'; /2/ by conj;
##|##4,5: #r1 r2 IH1 IH2 a'; ncases a'; nnormalize; /2/ by conj;
##|#r IH a'; ncases a'; nnormalize; /2/ by conj; ##]
nqed.

unification hint 0 ≔ S:Alpha, A,B:re (carr (acarr S));
    SS ≟ carr (acarr S),
    MM ≟ mk_unary_morphism ?? (λA.
           mk_unary_morphism ?? 
             (λB.A + B) (prop1 ?? (fun1 ?? (o_is_morph S) A)))
           (prop1 ?? (o_is_morph S)),
    T ≟ RE S
(*--------------------------------------------------------------------------*) ⊢
   fun1 T T (fun1 T (unary_morph_setoid T T) MM A) B ≡ o SS A B.

(* end setoids support for re *)

nlet rec conjunct S (l : list (list S)) (L : lang S) on l: CProp[0] ≝
match l with [ nil ⇒ True | cons w tl ⇒ w ∈ L ∧ conjunct ? tl L ].

interpretation "subset construction with type" 'comprehension t \eta.x = 
  (mk_powerclass t x).

ndefinition cat : ∀A:setoid.∀l1,l2:lang A.lang A ≝ 
  λS.λl1,l2.{ w ∈ list S | ∃w1,w2.w =_0 w1 @ w2 ∧ w1 ∈ l1 ∧ w2 ∈ l2}.
interpretation "cat lang" 'pc a b = (cat ? a b).

(* hints for cat *)
nlemma cat_is_morph : ∀A:setoid. (lang A) ⇒_1 (lang A) ⇒_1 (lang A).
#X; napply (mk_binary_morphism1 … (λA,B:lang X.A · B));
#A1 A2 B1 B2 EA EB; napply ext_set; #x;
ncut (∀y,x:list X.(x ∈ B1) =_1 (x ∈ B2)); ##[
  #_; #y; ncases EA; ncases EB; #h1 h2 h3 h4; @; ##[ napply h1 | napply h2] ##] #YY;
ncut (∀x,y:list X.(x ∈ A1) =_1 (x ∈ A2)); ##[
  #y; #y; ncases EA; ncases EB; #h1 h2 h3 h4; @; ##[ napply h3 | napply h4] ##] #XX;
napply (.=_1 (∑w1, w2. XX w1 w2/ E ; (# ╪_1 E) ╪_1 #));
napply (.=_1 (∑w1, w2. YY w1 w2/ E ; # ╪_1 E)); //;
nqed.

nlemma cat_is_ext: ∀A:setoid. (Elang A) → (Elang A) → (Elang A).
 #S A B; @ (ext_carr … A · ext_carr … B); (* XXX coercion ext_carr che non funge *)
#x y Exy;
ncut (∀w1,w2.(x == w1@w2) = (y == w1@w2)); ##[
  #w1 w2; @; #H; ##[ napply (.= Exy^-1) | napply (.= Exy)] // ] 
#E; @; #H;
##[ napply (. (∑w1,w2. (E w1 w2)^-1 / E ; (E ╪_1 #) ╪_1 #)); napply H;
##| napply (. (∑w1,w2. E w1 w2 / E ; (E ╪_1 #) ╪_1 #)); napply H ]
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, B,C : Elang A;
   AA ≟ LIST A,
   BB ≟ ext_carr AA B,
   CC ≟ ext_carr AA C,
   R ≟ mk_ext_powerclass AA
         (cat A (ext_carr AA B) (ext_carr AA C)) 
         (ext_prop AA (cat_is_ext A B C))
(*----------------------------------------------------------*)  ⊢
    ext_carr AA R ≡ cat A BB CC.
    
unification hint 0 ≔ S:setoid, A,B:lang (carr S);
    T ≟ powerclass_setoid (list (carr S)),
    MM ≟ mk_unary_morphism1 T (unary_morphism1_setoid1 T T)
          (λA:lang (carr S).
             mk_unary_morphism1 T T 
               (λB:lang (carr S).cat S A B) 
               (prop11 T T (fun11 ?? (cat_is_morph S) A)))
          (prop11 T (unary_morphism1_setoid1 T T) (cat_is_morph S))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T T (fun11 T (unary_morphism1_setoid1 T T) MM A) B ≡ cat S A B.
   
nlemma cat_is_ext_morph:∀A:setoid.(Elang A) ⇒_1 (Elang A) ⇒_1 (Elang A).
#A; napply (mk_binary_morphism1 …  (cat_is_ext …));
#x1 x2 y1 y2 Ex Ey; napply (prop11 … (cat_is_morph A)); nassumption.
nqed.

unification hint 1 ≔ AA : setoid, B,C : Elang AA;
  AAS ≟ LIST AA,
  T ≟ ext_powerclass_setoid AAS,
  R ≟ mk_unary_morphism1 T (unary_morphism1_setoid1 T T) (λX:Elang AA.
           mk_unary_morphism1 T T (λY:Elang AA.
             mk_ext_powerclass AAS 
               (cat AA (ext_carr ? X) (ext_carr ? Y)) 
               (ext_prop AAS (cat_is_ext AA X Y)))
             (prop11 T T (fun11 ?? (cat_is_ext_morph AA) X)))
           (prop11 T (unary_morphism1_setoid1 T T) (cat_is_ext_morph AA)),
   BB ≟ ext_carr ? B,
   CC ≟ ext_carr ? C
(*------------------------------------------------------*) ⊢
   ext_carr AAS (fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R B) C) ≡ cat AA BB CC.

(* end hints for cat *)

ndefinition star : ∀A:setoid.∀l:lang A.lang A ≝ 
  λS.λl.{ w ∈ list S | ∃lw.flatten ? lw = w ∧ conjunct ? lw l}. 
interpretation "star lang" 'pk l = (star ? l).

(* hints for star *)
nlemma star_is_morph : ∀A:setoid. (lang A) ⇒_1 (lang A).
#X; @(λA:lang X.A^* ); #a1 a2 E; @; #x; *; #wl; *; #defx Px; @wl; @; //;
nelim wl in Px; //; #s tl IH; *; #a1s a1tl; /4/; nqed.

nlemma star_is_ext: ∀A:setoid. (Elang A) → (Elang A).
 #S A; @ ((ext_carr … A) ^* ); #w1 w2 E; @; *; #wl; *; #defw1 Pwl;
 @wl; @; //; napply (.=_0 defw1); /2/; nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, B :  Elang A;
   AA ≟ LIST A,
   BB ≟ ext_carr AA B,
   R ≟ mk_ext_powerclass ? 
         ((ext_carr ? B)^* ) (ext_prop ? (star_is_ext ? B))
(*--------------------------------------------------------------------*)  ⊢
    ext_carr AA R ≡ star A BB.
    
unification hint 0 ≔ S:setoid, A:lang (carr S);
    T ≟ powerclass_setoid (list (carr S)),
    MM ≟ mk_unary_morphism1 T T 
               (λB:lang (carr S).star S B) (prop11 T T (star_is_morph S))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T T MM A ≡ star S A.
   
nlemma star_is_ext_morph:∀A:setoid.(Elang A) ⇒_1 (Elang A).
#A; @(star_is_ext …);
#x1 x2 Ex; napply (prop11 … (star_is_morph A)); nassumption.
nqed.

unification hint 1 ≔ AA : setoid, B : Elang AA;
  AAS ≟ LIST AA,
  T ≟ ext_powerclass_setoid AAS,
  R ≟ mk_unary_morphism1 T T
            (λS:Elang AA.
              mk_ext_powerclass AAS (star AA (ext_carr ? S)) 
                (ext_prop AAS (star_is_ext AA S)))
            (prop11 T T (star_is_ext_morph AA)),
   BB ≟ ext_carr ? B
(*------------------------------------------------------*) ⊢
   ext_carr AAS (fun11 T T R B) ≡ star AA BB.

(* end hints for star *)

notation > "𝐋 term 70 E" non associative with precedence 75 for @{L_re ? $E}.
nlet rec L_re (S : Alpha) (r : re S) on r : lang S ≝ 
match r with
[ z ⇒ ∅
| e ⇒ { [ ] }
| s x ⇒ { [x] }
| c r1 r2 ⇒ 𝐋 r1 · 𝐋 r2
| o r1 r2 ⇒  𝐋 r1 ∪ 𝐋 r2
| k r1 ⇒ (𝐋 r1) ^*].
notation "𝐋 term 70 E" non associative with precedence 75 for @{'L_re $E}.
interpretation "in_l" 'L_re E = (L_re ? E).

(* support for 𝐋 as an extensional set *)
ndefinition L_re_is_ext : ∀S:Alpha.∀r:re S.Elang S.
#S r; @(𝐋 r); #w1 w2 E; nelim r; 
##[ ##1,2: /2/; @; #defw1; napply (.=_0 (defw1 : [ ] = ?)); //; napply (?^-1); //;
##| #x; @; #defw1; napply (.=_0 (defw1 : [x] = ?)); //; napply (?^-1); //;
##| #e1 e2 H1 H2; (* not shure I shoud Inline *)
    @; *; #s1; *; #s2; *; *; #defw1 s1L1 s2L2; 
    ##[ nlapply (trans … E^-1 defw1); #defw2; 
    ##| nlapply (trans … E defw1); #defw2; ##] @s1; @s2; /3/;
##| #e1 e2 H1 H2; napply (H1‡H2); (* good! *)
##| #e H; @; *; #l; *; #defw1 Pl; @l; @; //; napply (.=_1 defw1); /2/; ##]
nqed.

unification hint 0 ≔ S : Alpha,e : re (carr (acarr S)); 
  SS ≟ LIST (acarr S),
  X ≟ mk_ext_powerclass SS (𝐋 e) (ext_prop SS (L_re_is_ext S e))
(*-----------------------------------------------------------------*)⊢ 
  ext_carr SS X ≡ L_re S e.

nlemma L_re_is_morph:∀A:Alpha.(setoid1_of_setoid (re A)) ⇒_1 Ω^(list A).
#A; @; ##[ napply (λr:re A.𝐋 r); ##] #r1; nelim r1;
##[##1,2: #r2; ncases r2; //; ##[##1,6: *|##2,7,5,12,10: #a; *|##3,4,8,9: #a1 a2; *]
##|#x r2; ncases r2; ##[##1,2: *|##4,5: #a1 a2; *|##6: #a; *] #y E; @; #z defz;
   ncases z in defz; ##[##1,3: *] #zh ztl; ncases ztl; ##[##2,4: #d dl; *; #_; *]
   *; #defx; #_; @; //; napply (?^-1); napply (.= defx^-1); //; napply (?^-1); //;
##|#e1 e2 IH1 IH2 r2; ncases r2; ##[##1,2: *|##5: #a1 a2; *|##3,6: #a1; *]
   #f1 f2; *; #E1 E2; nlapply (IH2 … E2); nlapply (IH1 … E1); #H1 H2;
   nchange in match (𝐋 (e1 · e2)) with (?·?);
   napply (.=_1 (H1 ╪_1 H2)); //;
##|#e1 e2 IH1 IH2 r2; ncases r2; ##[##1,2: *|##4: #a1 a2; *|##3,6: #a1; *]
   #f1 f2; *; #E1 E2; nlapply (IH2 … E2); nlapply (IH1 … E1); #H1 H2;
   napply (.=_1 H1╪_1H2); //;
##|#r IH r2; ncases r2; ##[##1,2: *|##4,5: #a1 a2; *|##3: #a1; *]
   #e; #defe; nlapply (IH e defe); #H;
   @; #x; *; #wl; *; #defx Px; @wl; @; //; nelim wl in Px; //; #l ls IH; *; #lr Pr;
   ##[ nlapply (ifs' … H … lr) | nlapply (ifs' … H^-1 … lr) ] #le; 
   @; ##[##1,3: nassumption] /2/; ##]
nqed.

unification hint 0 ≔ A:Alpha, a:re (carr (acarr A));
  T ≟ setoid1_of_setoid (RE A),
  T2 ≟ powerclass_setoid (list (carr (acarr A))),
  MM ≟ mk_unary_morphism1 ?? 
         (λa:carr1 (setoid1_of_setoid (RE A)).𝐋 a) (prop11 ?? (L_re_is_morph A))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T T2 MM a ≡  L_re A a.
   
nlemma L_re_is_ext_morph:∀A:Alpha.(setoid1_of_setoid (re A)) ⇒_1 𝛀^(list A).
#A; @; ##[ #a; napply (L_re_is_ext ? a); ##] #a b E;
ncut (𝐋 b =  𝐋 a); ##[ napply (.=_1 (┼_1 E^-1)); // ] #EL;
@; #x H; nchange in H ⊢ % with (x ∈ 𝐋 ?); 
##[ napply (. (# ╪_1 ?)); ##[##3: napply H |##2: ##skip ] napply EL;
##| napply (. (# ╪_1 ?)); ##[##3: napply H |##2: ##skip ] napply (EL^-1)]
nqed.
            
unification hint 1 ≔  AA : Alpha, a: re (carr (acarr AA));
  T ≟ RE AA, T1 ≟ LIST (acarr AA), T2 ≟ setoid1_of_setoid T, 
  TT ≟ ext_powerclass_setoid T1,
  R ≟ mk_unary_morphism1 T2 TT
       (λa:carr1 (setoid1_of_setoid T).
         mk_ext_powerclass T1 (𝐋 a) (ext_prop T1 (L_re_is_ext AA a)))
            (prop11 T2 TT (L_re_is_ext_morph AA))
(*------------------------------------------------------*) ⊢
   ext_carr T1 (fun11 (setoid1_of_setoid T) TT R a) ≡ L_re AA a.

(* end support for 𝐋 as an extensional set *)

ninductive pitem (S: Type[0]) : Type[0] ≝
   pz: pitem S
 | pe: pitem S
 | ps: S → pitem S
 | pp: S → pitem S
 | pc: pitem S → pitem S → pitem S
 | po: pitem S → pitem S → pitem S
 | pk: pitem S → pitem S.
 
interpretation "pstar" 'pk a = (pk ? a).
interpretation "por" 'plus a b = (po ? a b).
interpretation "pcat" 'pc a b = (pc ? a b).
notation < ".a" non associative with precedence 90 for @{ 'pp $a}.
notation > "`. term 90 a" non associative with precedence 90 for @{ 'pp $a}.
interpretation "ppatom" 'pp a = (pp ? a).
(* to get rid of \middot *)
ncoercion pc : ∀S.∀p:pitem S. pitem S → pitem S  ≝ pc on _p : pitem ? to ∀_:?.?.
interpretation "patom" 'ps a = (ps ? a).
interpretation "pepsilon" 'epsilon = (pe ?).
interpretation "pempty" 'empty_r = (pz ?). 
 
(* setoids for pitem *)
nlet rec eq_pitem  (S : Alpha) (p1, p2 : pitem S) on p1 : CProp[0] ≝ 
 match p1 with
 [ pz ⇒ match p2 with [ pz ⇒ True | _ ⇒ False]
 | pe ⇒ match p2 with [ pe ⇒ True | _ ⇒ False]
 | ps x ⇒ match p2 with [ ps y ⇒ x = y | _ ⇒ False]
 | pp x ⇒ match p2 with [ pp y ⇒ x = y | _ ⇒ False]
 | pc a1 a2 ⇒ match p2 with [ pc b1 b2 ⇒ eq_pitem ? a1 b1 ∧ eq_pitem ? a2 b2| _ ⇒ False]
 | po a1 a2 ⇒ match p2 with [ po b1 b2 ⇒ eq_pitem ? a1 b1 ∧ eq_pitem ? a2 b2| _ ⇒ False]
 | pk a ⇒ match p2 with [ pk b ⇒ eq_pitem ? a b | _ ⇒ False]].
 
interpretation "eq_pitem" 'eq_low a b = (eq_pitem ? a b). 
 
nlemma PITEM : ∀S:Alpha.setoid.
#S; @(pitem S); @(eq_pitem …);
##[ #p; nelim p; //; nnormalize; #; @; //;
##| #p; nelim p; ##[##1,2: #y; ncases y; //; ##|##3,4: #x y; ncases y; //; #; napply (?^-1); nassumption;
    ##|##5,6: #r1 r2 H1 H2 p2; ncases p2; //; #s1 s2; nnormalize; *; #; @; /2/;
    ##| #r H y; ncases y; //; nnormalize; /2/;##]
##| #x; nelim x; 
    ##[ ##1,2: #y z; ncases y; ncases z; //; nnormalize; #; ncases (?:False); //;
    ##| ##3,4: #a; #y z; ncases y; ncases z; /2/; nnormalize; #; ncases (?:False); //;
    ##| ##5,6: #r1 r2 H1 H2 y z; ncases y; ncases z; //; nnormalize;
        ##[##1,2,5,6,7,8,4,10: #; ncases (?:False); //;##]
        #r1 r2 r3 r4; nnormalize; *; #H1 H2; *; #H3 H4; /3/;
    ##| #r H y z; ncases y; ncases z; //; nnormalize; ##[##1,2,3,4: #; ncases (?:False); //]
        #r2 r3; /3/; ##]##]
nqed.

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ SS:Alpha;
    S ≟ acarr SS,
    A ≟ carr S,
    P1 ≟ refl ? (eq0 (PITEM SS)),
    P2 ≟ sym ? (eq0 (PITEM SS)),
    P3 ≟ trans ? (eq0 (PITEM SS)),
    R ≟ mk_setoid (pitem (carr S)) 
         (mk_equivalence_relation (pitem A) (eq_pitem SS) P1 P2 P3)
(*-----------------------------------------------------------------*)⊢
    carr R ≡ pitem A.
    
unification hint 0 ≔ S:Alpha,a,b:pitem (carr (acarr S));
   R ≟ PITEM S,  L ≟ pitem (carr (acarr S))
(* -------------------------------------------- *) ⊢
   eq_pitem S a b ≡ eq_rel L (eq0 R) a b.    
    
(* end setoids for pitem *)

ndefinition pre ≝ λS.pitem S × bool.

notation "\fst term 90 x" non associative with precedence 90 for @{'fst $x}.
interpretation "fst" 'fst x = (fst ? ? x).
notation > "\snd term 90 x" non associative with precedence 90 for @{'snd $x}.
interpretation "snd" 'snd x = (snd ? ? x).

notation > "|term 19 e|" non associative with precedence 70 for @{forget ? $e}.
nlet rec forget (S: Alpha) (l : pitem S) on l: re S ≝
 match l with
  [ pz ⇒ 0
  | pe ⇒ ϵ
  | ps x ⇒ `x
  | pp x ⇒ `x
  | pc E1 E2 ⇒ (|E1| · |E2|)
  | po E1 E2 ⇒ (|E1| + |E2|)
  | pk E ⇒ |E|^* ].
  
notation < "|term 19 e|" non associative with precedence 70 for @{'forget $e}.
interpretation "forget" 'forget a = (forget ? a).

notation > "𝐋\p\ term 70 E" non associative with precedence 75 for @{L_pi ? $E}.
nlet rec L_pi (S : Alpha) (r : pitem S) on r : lang S ≝ 
match r with
[ pz ⇒ ∅
| pe ⇒ ∅
| ps _ ⇒ ∅
| pp x ⇒ { [x] }
| pc r1 r2 ⇒ 𝐋\p\ r1 · 𝐋 |r2| ∪ 𝐋\p\ r2
| po r1 r2 ⇒ 𝐋\p\ r1 ∪ 𝐋\p\ r2
| pk r1 ⇒ 𝐋\p\ r1 · 𝐋 (|r1|^* ) ].
notation > "𝐋\p term 70 E" non associative with precedence 75 for @{'L_pi $E}.
notation "𝐋\sub(\p) term 70 E" non associative with precedence 75 for @{'L_pi $E}.
interpretation "in_pl" 'L_pi E = (L_pi ? E).

(* set support for 𝐋\p *)
ndefinition L_pi_ext : ∀S:Alpha.∀r:pitem S.Elang S.
#S r; @(𝐋\p r); #w1 w2 E; nelim r; 
##[ ##1,2: /2/;
##| #x; @; *;
##| #x; @; #H; nchange in H with ([?] =_0 ?); ##[ napply ((.=_0 H) E); ##]
    napply ((.=_0 H) E^-1);
##| #e1 e2 H1 H2;
    napply (.= (#‡H2));
    ncut (∀x1,x2. (w1 = (x1@x2)) = (w2 = (x1@x2)));##[
      #x1 x2; @; #X; ##[ napply ((.= E^-1) X) | napply ((.= E) X) ] ##] #X;
    napply ((∑w1,w2. X w1 w2 / H ; (H╪_1#)╪_1#) ╪_1 #); 
##| #e1 e2 H1 H2; napply (H1‡H2); 
##| #e H; 
    ncut (∀x1,x2.(w1 = (x1@x2)) = (w2 = (x1@x2)));##[
      #x1 x2; @; #X; ##[ napply ((.= E^-1) X) | napply ((.= E) X) ] ##] #X;
    napply (∑w1,w2. X w1 w2 / H ; (H╪_1#)╪_1#); 
##]
nqed.

unification hint 0 ≔ S : Alpha,e : pitem (carr (acarr S)); 
  SS ≟ LIST (acarr S),
  X ≟ mk_ext_powerclass SS (𝐋\p e) (ext_prop SS (L_pi_ext S e))
(*-----------------------------------------------------------------*)⊢ 
  ext_carr SS X ≡ 𝐋\p e.

(* end set support for 𝐋\p *)  
  
ndefinition epsilon ≝ 
  λS:Alpha.λb.match b return λ_.lang S with [ true ⇒ { [ ] } | _ ⇒ ∅ ].

interpretation "epsilon" 'epsilon = (epsilon ?).
notation < "ϵ b" non associative with precedence 90 for @{'app_epsilon $b}.
interpretation "epsilon lang" 'app_epsilon b = (epsilon ? b).

(* hints for epsilon *)
nlemma epsilon_is_morph : ∀A:Alpha. (setoid1_of_setoid bool) ⇒_1 (lang A).
#X; @; ##[#b; napply(ϵ b)] #a1 a2; ncases a1; ncases a2; //; *; nqed.

nlemma epsilon_is_ext: ∀A:Alpha. (setoid1_of_setoid bool) → (Elang A).
 #S b; @(ϵ b); #w1 w2 E; ncases b; @; ##[##3,4:*] 
nchange in match (w1 ∈ ϵ true) with ([] =_0 w1);
nchange in match (w2 ∈ ϵ true) with ([] =_0 w2); #H; napply (.= H); /2/;
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : Alpha, B :  bool;
   AA ≟ LIST (acarr A),
   R ≟ mk_ext_powerclass ? 
         (ϵ B) (ext_prop ? (epsilon_is_ext ? B))
(*--------------------------------------------------------------------*)  ⊢
    ext_carr AA R ≡ epsilon A B.
    
unification hint 0 ≔ S:Alpha, A:bool;
    B ≟ setoid1_of_setoid BOOL,
    T ≟ powerclass_setoid (list (carr (acarr S))),
    MM ≟ mk_unary_morphism1 B T 
               (λB.ϵ B) (prop11 B T (epsilon_is_morph S))
(*--------------------------------------------------------------------------*) ⊢
   fun11 B T MM A ≡ epsilon S A.
   
nlemma epsilon_is_ext_morph:∀A:Alpha. (setoid1_of_setoid bool) ⇒_1 (Elang A).
#A; @(epsilon_is_ext …);
#x1 x2 Ex; napply (prop11 … (epsilon_is_morph A)); nassumption.
nqed.

unification hint 1 ≔ AA : Alpha, B : bool;
  AAS ≟ LIST (acarr AA), 
  BB ≟ setoid1_of_setoid BOOL,
  T ≟ ext_powerclass_setoid AAS,
  R ≟ mk_unary_morphism1 BB T
            (λS.
              mk_ext_powerclass AAS (epsilon AA S) 
                (ext_prop AAS (epsilon_is_ext AA S)))
            (prop11 BB T (epsilon_is_ext_morph AA))
(*------------------------------------------------------*) ⊢
   ext_carr AAS (fun11 BB T R B) ≡ epsilon AA B.

(* end hints for epsilon *)

ndefinition L_pr ≝ λS : Alpha.λp:pre S.  𝐋\p\ (\fst p) ∪ ϵ (\snd p).
  
interpretation "L_pr" 'L_pi E = (L_pr ? E).

nlemma append_eq_nil : ∀S:setoid.∀w1,w2:list S. [ ] = w1 @ w2 → w1 = [ ].
#S w1; ncases w1; //. nqed.
  
(* lemma 12 *) (* XXX: a case where Leibnitz equality could be exploited for H *)
nlemma epsilon_in_true : ∀S:Alpha.∀e:pre S. [ ] ∈ 𝐋\p e = (\snd e = true).
#S r; ncases r; #e b; @; ##[##2: #H; ncases b in H; ##[##2:*] #; @2; /2/; ##] 
ncases b; //; *; ##[##2:*] nelim e;
##[ ##1,2: *; ##| #c; *; ##| #c; *| ##7: #p H;
##| #r1 r2 H G; *; ##[##2: nassumption; ##]
##| #r1 r2 H1 H2; *; /2/ by {}]
*; #w1; *; #w2; *; *; 
##[ #defw1 H1 foo; napply H;
    napply (. (append_eq_nil ? ?? defw1)^-1╪_1#);
    nassumption; 
##| #defw1 H1 foo; napply H;
    napply (. (append_eq_nil ? ?? defw1)^-1╪_1#);
    nassumption; 
##]
nqed.

nlemma not_epsilon_lp : ∀S:Alpha.∀e:pitem S. ¬ ([ ] ∈ (𝐋\p e)).
#S e; nelim e; ##[##1,2,3,4: nnormalize;/2/]
##[ #p1 p2 np1 np2; *; ##[##2: napply np2] *; #w1; *; #w2; *; *; #abs;
    nlapply (append_eq_nil ??? abs); # defw1; #; napply np1;
    napply (. defw1^-1╪_1#);
    nassumption;
##| #p1 p2 np1 np2; *; nchange with (¬?); //;
##| #r n; *; #w1; *; #w2; *; *; #abs; #; napply n;
    nlapply (append_eq_nil ??? abs); # defw1; #;
    napply (. defw1^-1╪_1#);
    nassumption;##]
nqed.

ndefinition lo ≝ λS:Alpha.λa,b:pre S.〈\fst a + \fst b,\snd a || \snd b〉.
notation "a ⊕ b" left associative with precedence 65 for @{'oplus $a $b}.
interpretation "oplus" 'oplus a b = (lo ? a b).

ndefinition lc ≝ λS:Alpha.λbcast:∀S:Alpha.∀E:pitem S.pre S.λa,b:pre S.
   match a with [ mk_pair e1 b1 ⇒
   match b1 with 
   [ false ⇒ 〈e1 · \fst b, \snd b〉 
   | true ⇒ 〈e1 · \fst (bcast ? (\fst b)),\snd b || \snd (bcast ? (\fst b))〉]].
   
notation < "a ⊙ b" left associative with precedence 65 for @{'lc $op $a $b}.
interpretation "lc" 'lc op a b = (lc ? op a b).
notation > "a ⊙ b" left associative with precedence 65 for @{'lc eclose $a $b}.

ndefinition lk ≝ λS:Alpha.λbcast:∀S:Alpha.∀E:pitem S.pre S.λa:pre S.
   match a with [ mk_pair e1 b1 ⇒
   match b1 with 
   [ false ⇒ 〈e1^*, false〉 
   | true ⇒ 〈(\fst (bcast ? e1))^*, true〉]].

notation < "a \sup ⊛" non associative with precedence 90 for @{'lk $op $a}.
interpretation "lk" 'lk op a = (lk ? op a).
notation > "a ^ ⊛" non associative with precedence 75 for @{'lk eclose $a}.

notation > "•" non associative with precedence 65 for @{eclose ?}.
nlet rec eclose (S: Alpha) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 0, false 〉
  | pe ⇒ 〈 ϵ,  true 〉
  | ps x ⇒ 〈 `.x, false 〉
  | pp x ⇒ 〈 `.x, false 〉
  | po E1 E2 ⇒ •E1 ⊕ •E2
  | pc E1 E2 ⇒ •E1 ⊙ 〈 E2, false 〉 
  | pk E ⇒ 〈(\fst (•E))^*,true〉].
notation < "• x" non associative with precedence 65 for @{'eclose $x}.
interpretation "eclose" 'eclose x = (eclose ? x).
notation > "• x" non associative with precedence 65 for @{'eclose $x}.

ndefinition reclose ≝ λS:Alpha.λp:pre S.let p' ≝ •\fst p in 〈\fst p',\snd p || \snd p'〉.
interpretation "reclose" 'eclose x = (reclose ? x).

nlemma epsilon_or : ∀S:Alpha.∀b1,b2. ϵ(b1 || b2) = ϵ b1 ∪ ϵ b2. ##[##2: napply S]
#S b1 b2; ncases b1; ncases b2; 
nchange in match (true || true) with true;
nchange in match (true || false) with true;
nchange in match (ϵ true) with {[]};
nchange in match (ϵ false) with ∅;
##[##1,4: napply ((cupID…)^-1);
##| napply ((cup0 ? {[]})^-1);
##| napply (.= (cup0 ? {[]})^-1); napply cupC; ##]
nqed.

(* theorem 16: 2 *)
nlemma oplus_cup : ∀S:Alpha.∀e1,e2:pre S.𝐋\p (e1 ⊕ e2) = 𝐋\p e1 ∪ 𝐋\p e2.
#S r1; ncases r1; #e1 b1 r2; ncases r2; #e2 b2;
napply (.=_1 #╪_1 (epsilon_or ???));
napply (.=_1 (cupA…)^-1);
napply (.=_1 (cupA…)╪_1#);
napply (.=_1 (#╪_1(cupC…))╪_1#);
napply (.=_1 (cupA…)^-1╪_1#);
napply (.=_1 (cupA…));
//;
nqed.


(* XXX problem: auto does not find # (refl) when it has a concrete == *)
nlemma odotEt : ∀S:Alpha.∀e1,e2:pitem S.∀b2:bool.
  〈e1,true〉 ⊙ 〈e2,b2〉 = 〈e1 · \fst (•e2),b2 || \snd (•e2)〉.
#S e1 e2 b2; ncases b2; @; /3/ by refl, conj, I; nqed.

(*
nlemma LcatE : ∀S:Alpha.∀e1,e2:pitem S.
  𝐋\p (e1 · e2) =  𝐋\p e1 · 𝐋  |e2| ∪ 𝐋\p e2. //; nqed.
*)

nlemma cup_dotD : ∀S:Alpha.∀p,q,r:lang S.(p ∪ q) · r = (p · r) ∪ (q · r). 
#S p q r; napply ext_set; #w; nnormalize; @; 
##[ *; #x; *; #y; *; *; #defw; *; /7/ by or_introl, or_intror, ex_intro, conj;
##| *; *; #x; *; #y; *; *; /7/ by or_introl, or_intror, ex_intro, conj; ##]
nqed.


nlemma erase_dot : ∀S:Alpha.∀e1,e2:pitem S.𝐋 |e1 · e2| =  𝐋 |e1| · 𝐋 |e2|.
#S e1 e2; napply ext_set; nnormalize; #w; @; *; #w1; *; #w2; *; *; /7/ by ex_intro, conj;
nqed.

nlemma erase_plus : ∀S:Alpha.∀e1,e2:pitem S.𝐋 |e1 + e2| =  𝐋 |e1| ∪ 𝐋 |e2|.
#S e1 e2; napply ext_set; nnormalize; #w; @; *; /4/ by or_introl, or_intror; nqed.

nlemma erase_star : ∀S:Alpha.∀e1:pitem S.𝐋 |e1|^* = 𝐋 |e1^*|. //; nqed.

nlemma mem_single : ∀S:setoid.∀a,b:S. a ∈ {(b)} → a = b.
#S a b; nnormalize; /2/; nqed.

nlemma cup_sub: ∀S.∀A,B:𝛀^S.∀x. ¬ (x ∈ A) → A ∪ (B - {(x)}) = (A ∪ B) - {(x)}.
#S A B x H; napply ext_set; #w; @; 
##[ *; ##[ #wa; @; ##[@;//] #H2; napply H; napply (. (mem_single ??? H2)^-1╪_1#); //]
    *; #wb nwn; @; ##[@2;//] //;
##| *; *; ##[ #wa nwn; @; //] #wb nwn; @2; @; //;##]
nqed.

nlemma sub0 : ∀S.∀a:Ω^S. a - ∅ = a.
#S a; napply ext_set; #w; nnormalize; @; /3/; *; //; nqed.

nlemma subK : ∀S.∀a:Ω^S. a - a = ∅.
#S a; napply ext_set; #w; nnormalize; @; *; /2/; nqed.

nlemma subW : ∀S.∀a,b:Ω^S.∀w.w ∈ (a - b) → w ∈ a.
#S a b w; nnormalize; *; //; nqed.

nlemma erase_bull : ∀S:Alpha.∀a:pitem S. |\fst (•a)| = |a|.
#S a; nelim a; // by {};
##[ #e1 e2 IH1 IH2;
    napply (?^-1); 
    napply (.=_0 (IH1^-1)╪_0 (IH2^-1));
    nchange in match (•(e1 · ?)) with (?⊙?);
    ncases (•e1); #e3 b; ncases b; ##[ nnormalize; ncases (•e2); /3/ by refl, conj]
    napply (.=_0 #╪_0 (IH2)); //;
##| #e1 e2 IH1 IH2; napply (?^-1);
    napply (.=_0 (IH1^-1)╪_0(IH2^-1));
    nchange in match (•(e1+?)) with (?⊕?);
    ncases (•e1); ncases (•e2); //]
nqed.

(*
nlemma eta_lp : ∀S:Alpha.∀p:pre S. 𝐋\p p = 𝐋\p 〈\fst p, \snd p〉.
#S p; ncases p; //; nqed.
*)

(* XXX coercion ext_carr non applica *)
nlemma epsilon_dot: ∀S:Alpha.∀p:Elang S. {[]} · (ext_carr ? p) = p. 
#S e; napply ext_set; #w; @; ##[##2: #Hw; @[]; @w; @; //; @; //; napply #; (* XXX auto *) ##]
*; #w1; *; #w2; *; *; #defw defw1 Hw2; 
napply (. defw╪_1#); 
napply (. ((defw1 : [ ] = ?)^-1 ╪_0 #)╪_1#);
napply Hw2; 
nqed.

(* XXX This seems to be a pattern for equations *)
alias symbol "hint_decl" (instance 1) = "hint_decl_CProp2".
unification hint 0 ≔ S : Alpha, x,y: re (carr (acarr S));
  SS ≟ RE S,
  TT ≟ setoid1_of_setoid SS,
  T ≟ carr1 TT
(*-----------------------------------------*) ⊢ 
  eq_re S x y ≡ eq_rel1 T (eq1 TT) x y.    
(* XXX the previous hint does not work *)

(* theorem 16: 1 → 3 *)
nlemma odot_dot_aux : ∀S:Alpha.∀e1,e2: pre S.
      𝐋\p (•(\fst e2)) =  𝐋\p (\fst e2) ∪ 𝐋 |\fst e2| → 
         𝐋\p (e1 ⊙ e2) =  𝐋\p e1 · 𝐋 |\fst e2| ∪ 𝐋\p e2.
#S e1 e2 th1; ncases e1; #e1' b1'; ncases b1';
##[ nchange in match (〈?,true〉⊙?) with 〈?,?〉; 
    nletin e2' ≝ (\fst e2); nletin b2' ≝ (\snd e2); 
    nletin e2'' ≝ (\fst (•(\fst e2))); nletin b2'' ≝ (\snd (•(\fst e2)));
    napply (.=_1 (# ╪_1 (epsilon_or …))); (* XXX … is too slow if combined with .= *)
    nchange in match b2'' with b2''; (* XXX some unfoldings happened *)
    nchange in match b2' with b2';
    napply (.=_1 (# ╪_1 (cupC …))); napply (.=_1 (cupA …)); 
    napply (.=_1 (# ╪_1 (cupA …)^-1)); (* XXX slow, but not because of disamb! *)
    ncut (𝐋\p e2'' ∪ ϵ b2'' =  𝐋\p e2' ∪ 𝐋  |e2'|); ##[
      napply (?^-1); napply (.=_1 th1^-1); //;##] #E;
    napply (.=_1 (# ╪_1 (E ╪_1 #)));
    napply (?^-1);
    napply (.=_1 (cup_dotD …) ╪_1 #);
    napply (.=_1 (# ╪_1 (epsilon_dot …)) ╪_1 #); 
    napply (?^-1);
    napply (.=_1 # ╪_1 ((cupC …) ╪_1 #));
    napply (.=_1 (cupA …)^-1);
    napply (.=_1 (cupA …)^-1 ╪_1 #);
    napply (.=_1 (cupA …));
    nlapply (erase_bull S e2'); #XX;
    napply (.=_1 (((# ╪_1 (┼_1 ?) )╪_1 #)╪_1 #)); ##[##2: napply XX; ##| ##skip]
    //;   
##| ncases e2; #e2' b2'; nchange in match (𝐋\p ?) with (?∪?∪?);
    napply (.=_1 (cupA…));
    napply (?^-1); nchange in match (𝐋\p 〈?,false〉) with (?∪?);
    napply (.=_1 ((cup0…)╪_1#)╪_1#);
    //]
nqed.



nlemma sub_dot_star : 
  ∀S:Alpha.∀X:Elang S.∀b. (X - ϵ b) · (ext_carr … X)^* ∪ {[]} = (ext_carr … X)^*.
#S X b; napply ext_set; #w; @;
##[ *; ##[##2: #defw; @[]; @; //]
    *; #w1; *; #w2; *; *; #defw sube; *; #lw; *; #flx cj;
    @ (w1 :: lw); @; ##[ napply (.=_0 # ╪_0 flx); napply (?^-1); //]
    @; //; napply (subW … sube);
##| *; #wl; *; #defw Pwl; napply (. (defw^-1 ╪_1 #));
    nelim wl in Pwl; /2/;
    #s tl IH; *; #Xs Ptl; ncases s in Xs; ##[ #; napply IH; //] #x xs Xxxs;
    @; @(x :: xs); @(flatten ? tl); @; 
      ##[ @; ##[ napply #] @; ##[nassumption] ncases b; *; ##]
    nelim tl in Ptl; ##[ #; @[]; /2/] #w ws IH; *; #Xw Pws; @(w :: ws); @; ##[ napply #]
    @; //;##]
nqed.

(* theorem 16: 1 *)
alias symbol "pc" (instance 13) = "cat lang".
alias symbol "in_pl" (instance 23) = "in_pl".
alias symbol "in_pl" (instance 5) = "in_pl".
alias symbol "eclose" (instance 21) = "eclose".
ntheorem bull_cup : ∀S:Alpha. ∀e:pitem S.  𝐋\p (•e) =  𝐋\p e ∪ 𝐋 |e|.
#S e; nelim e; //;
  ##[ #a; napply ext_set; #w; @; *; /3/ by or_introl, or_intror;
  ##| #a; napply ext_set; #w; @; *; /3/ by or_introl; *;
  ##| #e1 e2 IH1 IH2;  
      nchange in match (•(e1·e2)) with (•e1 ⊙ 〈e2,false〉);
      napply (.=_1 (odot_dot_aux ?? 〈e2,false〉 IH2));
      napply (.=_1 (IH1 ╪_1 #) ╪_1 #);
      napply (.=_1 (cup_dotD …) ╪_1 #);
      napply (.=_1 (cupA …));
      napply (.=_1 # ╪_1 ((erase_dot ???)^-1 ╪_1 (cup0 ??)));
      napply (.=_1 # ╪_1 (cupC…));
      napply (.=_1 (cupA …)^-1);
      //;
  ##| #e1 e2 IH1 IH2;
      nchange in match (•(?+?)) with (•e1 ⊕ •e2);
      napply (.=_1 (oplus_cup …));
      napply (.=_1 IH1 ╪_1 IH2);
      napply (.=_1 (cupA …));
      napply (.=_1 # ╪_1 (# ╪_1 (cupC…)));
      napply (.=_1 # ╪_1 (cupA ????)^-1);
      napply (.=_1 # ╪_1 (cupC…));
      napply (.=_1 (cupA ????)^-1);
      napply (.=_1 # ╪_1 (erase_plus ???)^-1);
      //;
  ##| #e; nletin e' ≝ (\fst (•e)); nletin b' ≝ (\snd (•e)); #IH;
      nchange in match (𝐋\p ?) with (𝐋\p 〈e'^*,true〉);
      nchange in match (𝐋\p ?) with (𝐋\p (e'^* ) ∪ {[ ]});
STOP
      nchange in match (𝐋\p (pk ? e')) with (𝐋\p e' · 𝐋  |e'|^* );
      nrewrite > (erase_bull…e);
      nrewrite > (erase_star …);
      nrewrite > (?: 𝐋\p e' =  𝐋\p e ∪ (𝐋 .|e| - ϵ b')); ##[##2:
        nchange in IH : (??%?) with (𝐋\p e' ∪ ϵ b'); ncases b' in IH; 
        ##[ #IH; nrewrite > (cup_sub…); //; nrewrite < IH; 
            nrewrite < (cup_sub…); //; nrewrite > (subK…); nrewrite > (cup0…);//;
        ##| nrewrite > (sub0 …); #IH; nrewrite < IH; nrewrite > (cup0 …);//; ##]##]
      nrewrite > (cup_dotD…); nrewrite > (cupA…); 
      nrewrite > (?: ((?·?)∪{[]} = 𝐋 .|e^*|)); //;
      nchange in match (𝐋 .|e^*|) with ((𝐋. |e|)^* ); napply sub_dot_star;##]
nqed.

(* theorem 16: 3 *)      
nlemma odot_dot: 
  ∀S.∀e1,e2: pre S.  𝐋\p (e1 ⊙ e2) =  𝐋\p e1 · 𝐋 .|\fst e2| ∪ 𝐋\p e2.
#S e1 e2; napply odot_dot_aux; napply (bull_cup S (\fst e2)); nqed.

nlemma dot_star_epsilon : ∀S.∀e:re S.𝐋 e · 𝐋 e^* ∪ {[]} =  𝐋 e^*.
#S e; napply extP; #w; nnormalize; @;
##[ *; ##[##2: #H; nrewrite < H; @[]; /3/] *; #w1; *; #w2; 
    *; *; #defw Hw1; *; #wl; *; #defw2 Hwl; @(w1 :: wl);
    nrewrite < defw; nrewrite < defw2; @; //; @;//;
##| *; #wl; *; #defw Hwl; ncases wl in defw Hwl; ##[#defw; #; @2; nrewrite < defw; //]
    #x xs defw; *; #Hx Hxs; @; @x; @(flatten ? xs); nrewrite < defw;
    @; /2/; @xs; /2/;##]
 nqed.

nlemma nil_star : ∀S.∀e:re S. [ ] ∈ e^*.
#S e; @[]; /2/; nqed.

nlemma cupID : ∀S.∀l:word S → Prop.l ∪ l = l.
#S l; napply extP; #w; @; ##[*]//; #; @; //; nqed.

nlemma cup_star_nil : ∀S.∀l:word S → Prop. l^* ∪ {[]} = l^*.
#S a; napply extP; #w; @; ##[*; //; #H; nrewrite < H; @[]; @; //] #;@; //;nqed.

nlemma rcanc_sing : ∀S.∀A,C:word S → Prop.∀b:word S .
  ¬ (A b) → A ∪ { (b) } = C → A = C - { (b) }.
#S A C b nbA defC; nrewrite < defC; napply extP; #w; @;
##[ #Aw; /3/| *; *; //; #H nH; ncases nH; #abs; nlapply (abs H); *]
nqed.

(* theorem 16: 4 *)      
nlemma star_dot: ∀S.∀e:pre S. 𝐋\p (e^⊛) = 𝐋\p e · (𝐋 .|\fst e|)^*.
#S p; ncases p; #e b; ncases b;
##[ nchange in match (〈e,true〉^⊛) with 〈?,?〉;
    nletin e' ≝ (\fst (•e)); nletin b' ≝ (\snd (•e));
    nchange in ⊢ (??%?) with (?∪?);
    nchange in ⊢ (??(??%?)?) with (𝐋\p e' · 𝐋 .|e'|^* );
    nrewrite > (?: 𝐋\p e' = 𝐋\p e ∪ (𝐋 .|e| - ϵ b' )); ##[##2:
      nlapply (bull_cup ? e); #bc;
      nchange in match (𝐋\p (•e)) in bc with (?∪?);
      nchange in match b' in bc with b';
      ncases b' in bc; ##[##2: nrewrite > (cup0…); nrewrite > (sub0…); //]
      nrewrite > (cup_sub…); ##[napply rcanc_sing] //;##]
    nrewrite > (cup_dotD…); nrewrite > (cupA…);nrewrite > (erase_bull…);
    nrewrite > (sub_dot_star…);
    nchange in match (𝐋\p 〈?,?〉) with (?∪?);
    nrewrite > (cup_dotD…); nrewrite > (epsilon_dot…); //;    
##| nwhd in match (〈e,false〉^⊛); nchange in match (𝐋\p 〈?,?〉) with (?∪?);
    nrewrite > (cup0…);
    nchange in ⊢ (??%?) with (𝐋\p e · 𝐋 .|e|^* );
    nrewrite < (cup0 ? (𝐋\p e)); //;##]
nqed.

nlet rec pre_of_re (S : Alpha) (e : re S) on e : pitem S ≝ 
  match e with 
  [ z ⇒ pz ?
  | e ⇒ pe ?
  | s x ⇒ ps ? x
  | c e1 e2 ⇒ pc ? (pre_of_re ? e1) (pre_of_re ? e2)
  | o e1 e2 ⇒ po ? (pre_of_re ? e1) (pre_of_re ? e2)
  | k e1 ⇒ pk ? (pre_of_re ? e1)].

nlemma notFalse : ¬False. @; //; nqed.

nlemma dot0 : ∀S.∀A:word S → Prop. {} · A = {}.
#S A; nnormalize; napply extP; #w; @; ##[##2: *]
*; #w1; *; #w2; *; *; //; nqed.

nlemma Lp_pre_of_re : ∀S.∀e:re S. 𝐋\p (pre_of_re ? e) = {}.
#S e; nelim e; ##[##1,2,3: //]
##[ #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1 e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (dot0…); nrewrite > (cupID…);//
##| #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1+e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (cupID…); //
##| #e1 H1; nchange in match (𝐋\p (pre_of_re S (e1^* ))) with (𝐋\p (pre_of_re ??) · ?);
    nrewrite > H1; napply dot0; ##]
nqed.

nlemma erase_pre_of_reK : ∀S.∀e. 𝐋 .|pre_of_re S e| = 𝐋 e.
#S A; nelim A; //; 
##[ #e1 e2 H1 H2; nchange in match (𝐋 (e1 · e2)) with (𝐋 e1·?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 e2 H1 H2; nchange in match (𝐋 (e1 + e2)) with (𝐋 e1 ∪ ?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 H1; nchange in match (𝐋  (e1^* )) with ((𝐋 e1)^* );
    nrewrite < H1; //]
nqed.     

(* corollary 17 *)
nlemma L_Lp_bull : ∀S.∀e:re S.𝐋 e = 𝐋\p (•pre_of_re ? e).
#S e; nrewrite > (bull_cup…); nrewrite > (Lp_pre_of_re…);
nrewrite > (cupC…); nrewrite > (cup0…); nrewrite > (erase_pre_of_reK…); //;
nqed.

nlemma Pext : ∀S.∀f,g:word S → Prop. f = g → ∀w.f w → g w.
#S f g H; nrewrite > H; //; nqed.
 
(* corollary 18 *)
ntheorem bull_true_epsilon : ∀S.∀e:pitem S. \snd (•e) = true ↔ [ ] ∈ .|e|.
#S e; @;
##[ #defsnde; nlapply (bull_cup ? e); nchange in match (𝐋\p (•e)) with (?∪?);
    nrewrite > defsnde; #H; 
    nlapply (Pext ??? H [ ] ?); ##[ @2; //] *; //;
    E MO?

STOP

notation > "\move term 90 x term 90 E" 
non associative with precedence 65 for @{move ? $x $E}.
nlet rec move (S: Alpha) (x:S) (E: pitem S) on E : pre S ≝
 match E with
  [ pz ⇒ 〈 ∅, false 〉
  | pe ⇒ 〈 ϵ, false 〉
  | ps y ⇒ 〈 `y, false 〉
  | pp y ⇒ 〈 `y, x == y 〉
  | po e1 e2 ⇒ \move x e1 ⊕ \move x e2 
  | pc e1 e2 ⇒ \move x e1 ⊙ \move x e2
  | pk e ⇒ (\move x e)^⊛ ].
notation < "\move\shy x\shy E" non associative with precedence 65 for @{'move $x $E}.
notation > "\move term 90 x term 90 E" non associative with precedence 65 for @{'move $x $E}.
interpretation "move" 'move x E = (move ? x E).

ndefinition rmove ≝ λS:Alpha.λx:S.λe:pre S. \move x (\fst e).
interpretation "rmove" 'move x E = (rmove ? x E).

nlemma XXz :  ∀S:Alpha.∀w:word S. w .∈ ∅ → False.
#S w abs; ninversion abs; #; ndestruct;
nqed.


nlemma XXe :  ∀S:Alpha.∀w:word S. w .∈ ϵ → False.
#S w abs; ninversion abs; #; ndestruct;
nqed.

nlemma XXze :  ∀S:Alpha.∀w:word S. w .∈ (∅ · ϵ)  → False.
#S w abs; ninversion abs; #; ndestruct; /2/ by XXz,XXe;
nqed.


naxiom in_move_cat:
 ∀S.∀w:word S.∀x.∀E1,E2:pitem S. w .∈ \move x (E1 · E2) → 
   (∃w1.∃w2. w = w1@w2 ∧ w1 .∈ \move x E1 ∧ w2 ∈ .|E2|) ∨ w .∈ \move x E2.
#S w x e1 e2 H; nchange in H with (w .∈ \move x e1 ⊙ \move x e2);
ncases e1 in H; ncases e2;
##[##1: *; ##[*; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz,XXze;
##|##2: *; ##[*; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz,XXze;
##| #r; *; ##[ *; nnormalize; #; ndestruct] 
   #H; ninversion H; ##[##1,4,5,6: nnormalize; #; ndestruct]
   ##[##2: nnormalize; #; ndestruct; @2; @2; //.##]
   nnormalize; #; ndestruct; ncases (?:False); /2/ by XXz;
##| #y; *; ##[ *; nnormalize; #defw defx; ndestruct; @2; @1; /2/ by conj;##]
   #H; ninversion H; nnormalize; #; ndestruct; 
   ##[ncases (?:False); /2/ by XXz] /3/ by or_intror;
##| #r1 r2; *; ##[ *; #defw]
    ...
nqed.

ntheorem move_ok:
 ∀S:Alpha.∀E:pre S.∀a,w.w .∈ \move a E ↔ (a :: w) .∈ E. 
#S E; ncases E; #r b; nelim r;
##[##1,2: #a w; @; 
   ##[##1,3: nnormalize; *; ##[##1,3: *; #; ndestruct; ##| #abs; ncases (XXz … abs); ##]
      #H; ninversion H; #; ndestruct;
   ##|##*:nnormalize; *; ##[##1,3: *; #; ndestruct; ##| #H1; ncases (XXz … H1); ##]
       #H; ninversion H; #; ndestruct;##]
##|#a c w; @; nnormalize; ##[*; ##[*; #; ndestruct; ##] #abs; ninversion abs; #; ndestruct;##]
   *; ##[##2: #abs; ninversion abs; #; ndestruct; ##] *; #; ndestruct;
##|#a c w; @; nnormalize; 
   ##[ *; ##[ *; #defw; nrewrite > defw; #ca; @2;  nrewrite > (eqb_t … ca); @; ##]
       #H; ninversion H; #; ndestruct;
   ##| *; ##[ *; #; ndestruct; ##] #H; ninversion H; ##[##2,3,4,5,6: #; ndestruct]
              #d defw defa; ndestruct; @1; @; //; nrewrite > (eqb_true S d d); //. ##]
##|#r1 r2 H1 H2 a w; @;
   ##[ #H; ncases (in_move_cat … H);
      ##[ *; #w1; *; #w2; *; *; #defw w1m w2m;
          ncases (H1 a w1); #H1w1; #_; nlapply (H1w1 w1m); #good; 
          nrewrite > defw; @2; @2 (a::w1); //; ncases good; ##[ *; #; ndestruct] //.
      ##|
      ...
##|
##|
##]
nqed.


notation > "x ↦* E" non associative with precedence 65 for @{move_star ? $x $E}.
nlet rec move_star (S : decidable) w E on w : bool × (pre S) ≝
 match w with
  [ nil ⇒ E
  | cons x w' ⇒ w' ↦* (x ↦ \snd E)].

ndefinition in_moves ≝ λS:decidable.λw.λE:bool × (pre S). \fst(w ↦* E).

ncoinductive equiv (S:decidable) : bool × (pre S) → bool × (pre S) → Prop ≝
 mk_equiv:
  ∀E1,E2: bool × (pre S).
   \fst E1  = \fst E2 →
    (∀x. equiv S (x ↦ \snd E1) (x ↦ \snd E2)) →
     equiv S E1 E2.

ndefinition NAT: decidable.
 @ nat eqb; /2/.
nqed.

include "hints_declaration.ma".

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ ; X ≟ NAT ⊢ carr X ≡ nat.

ninductive unit: Type[0] ≝ I: unit.

nlet corec foo_nop (b: bool):
 equiv ?
  〈 b, pc ? (ps ? 0) (pk ? (pc ? (ps ? 1) (ps ? 0))) 〉
  〈 b, pc ? (pk ? (pc ? (ps ? 0) (ps ? 1))) (ps ? 0) 〉 ≝ ?.
 @; //; #x; ncases x
  [ nnormalize in ⊢ (??%%); napply (foo_nop false)
  | #y; ncases y
     [ nnormalize in ⊢ (??%%); napply (foo_nop false)
     | #w; nnormalize in ⊢ (??%%); napply (foo_nop false) ]##]
nqed.

(*
nlet corec foo (a: unit):
 equiv NAT
  (eclose NAT (pc ? (ps ? 0) (pk ? (pc ? (ps ? 1) (ps ? 0)))))
  (eclose NAT (pc ? (pk ? (pc ? (ps ? 0) (ps ? 1))) (ps ? 0)))
≝ ?.
 @;
  ##[ nnormalize; //
  ##| #x; ncases x
       [ nnormalize in ⊢ (??%%);
         nnormalize in foo: (? → ??%%);
         @; //; #y; ncases y
           [ nnormalize in ⊢ (??%%); napply foo_nop
           | #y; ncases y
              [ nnormalize in ⊢ (??%%);
                
            ##| #z; nnormalize in ⊢ (??%%); napply foo_nop ]##]
     ##| #y; nnormalize in ⊢ (??%%); napply foo_nop
  ##]
nqed.
*)

ndefinition test1 : pre ? ≝ ❨ `0 | `1 ❩^* `0.
ndefinition test2 : pre ? ≝ ❨ (`0`1)^* `0 | (`0`1)^* `1 ❩.
ndefinition test3 : pre ? ≝ (`0 (`0`1)^* `1)^*.


nlemma foo: in_moves ? [0;0;1;0;1;1] (ɛ test3) = true.
 nnormalize in match test3;
 nnormalize;
//;
nqed.

(**********************************************************)

ninductive der (S: Type[0]) (a: S) : re S → re S → CProp[0] ≝
   der_z: der S a (z S) (z S)
 | der_e: der S a (e S) (z S)
 | der_s1: der S a (s S a) (e ?)
 | der_s2: ∀b. a ≠ b → der S a (s S b) (z S)
 | der_c1: ∀e1,e2,e1',e2'. in_l S [] e1 → der S a e1 e1' → der S a e2 e2' →
            der S a (c ? e1 e2) (o ? (c ? e1' e2) e2')
 | der_c2: ∀e1,e2,e1'. Not (in_l S [] e1) → der S a e1 e1' →
            der S a (c ? e1 e2) (c ? e1' e2)
 | der_o: ∀e1,e2,e1',e2'. der S a e1 e1' → der S a e2 e2' →
    der S a (o ? e1 e2) (o ? e1' e2').

nlemma eq_rect_CProp0_r:
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → CProp[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; ncases p; #P; #H; nassumption.
nqed.

nlemma append1: ∀A.∀a:A.∀l. [a] @ l = a::l. //. nqed.

naxiom in_l1: ∀S,r1,r2,w. in_l S [ ] r1 → in_l S w r2 → in_l S w (c S r1 r2).
(* #S; #r1; #r2; #w; nelim r1
  [ #K; ninversion K
  | #H1; #H2; napply (in_c ? []); //
  | (* tutti casi assurdi *) *)

ninductive in_l' (S: Type[0]) : word S → re S → CProp[0] ≝
   in_l_empty1: ∀E.in_l S [] E → in_l' S [] E 
 | in_l_cons: ∀a,w,e,e'. in_l' S w e' → der S a e e' → in_l' S (a::w) e.

ncoinductive eq_re (S: Type[0]) : re S → re S → CProp[0] ≝
   mk_eq_re: ∀E1,E2.
    (in_l S [] E1 → in_l S [] E2) →
    (in_l S [] E2 → in_l S [] E1) →
    (∀a,E1',E2'. der S a E1 E1' → der S a E2 E2' → eq_re S E1' E2') →
      eq_re S E1 E2.

(* serve il lemma dopo? *)
ntheorem eq_re_is_eq: ∀S.∀E1,E2. eq_re S E1 E2 → ∀w. in_l ? w E1 → in_l ? w E2.
 #S; #E1; #E2; #H1; #w; #H2; nelim H2 in E2 H1 ⊢ %
  [ #r; #K (* ok *)
  | #a; #w; #R1; #R2; #K1; #K2; #K3; #R3; #K4; @2 R2; //; ncases K4;

(* IL VICEVERSA NON VALE *)
naxiom in_l_to_in_l: ∀S,w,E. in_l' S w E → in_l S w E.
(* #S; #w; #E; #H; nelim H
  [ //
  | #a; #w'; #r; #r'; #H1; (* e si cade qua sotto! *)
  ]
nqed. *)

ntheorem der1: ∀S,a,e,e',w. der S a e e' → in_l S w e' → in_l S (a::w) e.
 #S; #a; #E; #E'; #w; #H; nelim H
  [##1,2: #H1; ninversion H1
     [##1,8: #_; #K; (* non va ndestruct K; *) ncases (?:False); (* perche' due goal?*) /2/
     |##2,9: #X; #Y; #K; ncases (?:False); /2/
     |##3,10: #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     |##4,11: #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     |##5,12: #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     |##6,13: #x; #y; #K; ncases (?:False); /2/
     |##7,14: #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/]
##| #H1; ninversion H1
     [ //
     | #X; #Y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/ ]
##| #H1; #H2; #H3; ninversion H3
     [ #_; #K; ncases (?:False); /2/
     | #X; #Y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #e; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #K; ncases (?:False); /2/
     | #x; #y; #K; ncases (?:False); /2/
     | #x; #y; #z; #w; #a; #b; #c; #d; #K; ncases (?:False); /2/ ]
##| #r1; #r2; #r1'; #r2'; #H1; #H2; #H3; #H4; #H5; #H6;

