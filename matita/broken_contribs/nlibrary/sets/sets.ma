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

(******************* SETS OVER TYPES *****************)

include "logic/connectives.ma".

nrecord powerclass (A: Type[0]) : Type[1] ≝ { mem: A → CProp[0] }.

interpretation "mem" 'mem a S = (mem ? S a).
interpretation "powerclass" 'powerset A = (powerclass A).
interpretation "subset construction" 'subset \eta.x = (mk_powerclass ? x).

ndefinition subseteq ≝ λA.λU,V.∀a:A. a ∈ U → a ∈ V.
interpretation "subseteq" 'subseteq U V = (subseteq ? U V).

ndefinition overlaps ≝ λA.λU,V.∃x:A.x ∈ U ∧ x ∈ V.
interpretation "overlaps" 'overlaps U V = (overlaps ? U V).

ndefinition intersect ≝ λA.λU,V:Ω^A.{ x | x ∈ U ∧ x ∈ V }.
interpretation "intersect" 'intersects U V = (intersect ? U V).

ndefinition union ≝ λA.λU,V:Ω^A.{ x | x ∈ U ∨ x ∈ V }.
interpretation "union" 'union U V = (union ? U V).

ndefinition substract ≝ λA.λU,V:Ω^A.{ x | x ∈ U ∧ ¬ x ∈ V }.
interpretation "substract" 'minus U V = (substract ? U V).


ndefinition big_union ≝ λA,B.λT:Ω^A.λf:A → Ω^B.{ x | ∃i. i ∈ T ∧ x ∈ f i }.

ndefinition big_intersection ≝ λA,B.λT:Ω^A.λf:A → Ω^B.{ x | ∀i. i ∈ T → x ∈ f i }.

ndefinition full_set: ∀A. Ω^A ≝ λA.{ x | True }.

nlemma subseteq_refl: ∀A.∀S: Ω^A. S ⊆ S.
//.nqed.

nlemma subseteq_trans: ∀A.∀S,T,U: Ω^A. S ⊆ T → T ⊆ U → S ⊆ U.
/3/.nqed.

include "properties/relations1.ma".

ndefinition seteq: ∀A. equivalence_relation1 (Ω^A).
#A; @(λS,S'. S ⊆ S' ∧ S' ⊆ S); /2/; ##[ #A B; *; /3/]
#S T U; *; #H1 H2; *; /4/;
nqed.

include "sets/setoids1.ma".

ndefinition singleton ≝ λA:setoid.λa:A.{ x | a = x }.
interpretation "singl" 'singl a = (singleton ? a).

(* this has to be declared here, so that it is combined with carr *)
ncoercion full_set : ∀A:Type[0]. Ω^A ≝ full_set on A: Type[0] to (Ω^?).

ndefinition powerclass_setoid: Type[0] → setoid1.
 #A; @(Ω^A);//.
nqed.

alias symbol "hint_decl" = "hint_decl_Type2".
unification hint 0 ≔ A;
  R ≟ (mk_setoid1 (Ω^A) (eq1 (powerclass_setoid A)))
(*--------------------------------------------------*)⊢ 
     carr1 R ≡ Ω^A.

(************ SETS OVER SETOIDS ********************)

include "logic/cprop.ma".

nrecord ext_powerclass (A: setoid) : Type[1] ≝ { 
   ext_carr:> Ω^A; (* qui pc viene dichiarato con un target preciso... 
                      forse lo si vorrebbe dichiarato con un target più lasco 
                      ma la sintassi :> non lo supporta *)
   ext_prop: ∀x,x':A. x=x' → (x ∈ ext_carr) = (x' ∈ ext_carr) 
}.
 
notation > "𝛀 ^ term 90 A" non associative with precedence 70 
for @{ 'ext_powerclass $A }.

notation < "Ω term 90 A \atop ≈" non associative with precedence 90 
for @{ 'ext_powerclass $A }.

interpretation "extensional powerclass" 'ext_powerclass a = (ext_powerclass a).

ndefinition Full_set: ∀A. 𝛀^A.
 #A; @[ napply A | #x; #x'; #H; napply refl1]
nqed.
ncoercion Full_set: ∀A. ext_powerclass A ≝ Full_set on A: setoid to ext_powerclass ?.

ndefinition ext_seteq: ∀A. equivalence_relation1 (𝛀^A).
 #A; @ [ napply (λS,S'. S = S') ] /2/.
nqed.

ndefinition ext_powerclass_setoid: setoid → setoid1.
 #A; @ (ext_seteq A).
nqed.
              
unification hint 0 ≔ A;
      R ≟ (mk_setoid1 (𝛀^A) (eq1 (ext_powerclass_setoid A)))
  (* ----------------------------------------------------- *) ⊢  
                 carr1 R ≡ ext_powerclass A.

nlemma mem_ext_powerclass_setoid_is_morph: 
 ∀A. (setoid1_of_setoid A) ⇒_1 ((𝛀^A) ⇒_1 CPROP).
#A; napply (mk_binary_morphism1 … (λx:setoid1_of_setoid A.λS: 𝛀^A. x ∈ S));
#a; #a'; #b; #b'; #Ha; *; #Hb1; #Hb2; @; #H
[ napply (. (ext_prop … Ha^-1)) | napply (. (ext_prop … Ha)) ] /2/.
nqed.

unification hint 0 ≔  AA : setoid, S : 𝛀^AA, x : carr AA;  
     A ≟ carr AA,
     SS ≟ (ext_carr ? S),
     TT ≟ (mk_unary_morphism1 ?? 
             (λx:carr1 (setoid1_of_setoid ?).
               mk_unary_morphism1 ??
                 (λS:carr1 (ext_powerclass_setoid ?). x ∈ (ext_carr ? S))
                 (prop11 ?? (fun11 ?? (mem_ext_powerclass_setoid_is_morph AA) x)))
             (prop11 ?? (mem_ext_powerclass_setoid_is_morph AA))),
     T2 ≟ (ext_powerclass_setoid AA)
(*---------------------------------------------------------------------------*) ⊢ 
    fun11 T2 CPROP (fun11 (setoid1_of_setoid AA) (unary_morphism1_setoid1 T2 CPROP) TT x) S ≡ mem A SS x.

nlemma set_ext : ∀S.∀A,B:Ω^S.A =_1 B → ∀x:S.(x ∈ A) =_1 (x ∈ B).
#S A B; *; #H1 H2 x; @; ##[ napply H1 | napply H2] nqed.

nlemma ext_set : ∀S.∀A,B:Ω^S.(∀x:S. (x ∈ A) = (x ∈ B)) → A = B.
#S A B H; @; #x; ncases (H x); #H1 H2; ##[ napply H1 | napply H2] nqed.

nlemma subseteq_is_morph: ∀A.  𝛀^A ⇒_1 𝛀^A ⇒_1 CPROP.
 #A; napply (mk_binary_morphism1 … (λS,S':𝛀^A. S ⊆ S'));
 #a; #a'; #b; #b'; *; #H1; #H2; *; /5/ by mk_iff, sym1, subseteq_trans;
nqed.

(* hints for ∩ *)
nlemma intersect_is_ext: ∀A. 𝛀^A → 𝛀^A → 𝛀^A.
#S A B; @ (A ∩ B); #x y Exy; @; *; #H1 H2; @;
##[##1,2: napply (. Exy^-1╪_1#); nassumption;
##|##3,4: napply (. Exy‡#); nassumption]
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, B,C : 𝛀^A;
  AA ≟ carr A,
  BB ≟ ext_carr ? B,
  CC ≟ ext_carr ? C,
  R ≟ (mk_ext_powerclass ? 
        (ext_carr ? B ∩ ext_carr ? C) 
        (ext_prop ? (intersect_is_ext ? B C))) 
  (* ------------------------------------------*)  ⊢ 
    ext_carr A R ≡ intersect AA BB CC.
    
nlemma intersect_is_morph: ∀A. Ω^A ⇒_1 Ω^A ⇒_1 Ω^A.
#A; napply (mk_binary_morphism1 … (λS,S'. S ∩ S'));
#a; #a'; #b; #b'; *; #Ha1; #Ha2; *; #Hb1; #Hb2; @; #x; nnormalize; *;/3/.
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : Type[0], B,C : Ω^A;
  T ≟ powerclass_setoid A,
  R ≟ mk_unary_morphism1 ??
       (λX. mk_unary_morphism1 ?? 
         (λY.X ∩ Y) (prop11 ?? (fun11 ?? (intersect_is_morph A) X))) 
       (prop11 ?? (intersect_is_morph A))
(*------------------------------------------------------------------------*) ⊢ 
    fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R B) C  ≡ intersect A B C.

interpretation "prop21 ext" 'prop2 l r =
 (prop11 (ext_powerclass_setoid ?)
  (unary_morphism1_setoid1 (ext_powerclass_setoid ?) ?) ? ?? l ?? r).

nlemma intersect_is_ext_morph: ∀A. 𝛀^A ⇒_1 𝛀^A ⇒_1 𝛀^A.
 #A; napply (mk_binary_morphism1 … (intersect_is_ext …));
 #a; #a'; #b; #b'; #Ha; #Hb; napply (prop11 … (intersect_is_morph A)); nassumption.
nqed.

unification hint 1 ≔ 
      AA : setoid, B,C : 𝛀^AA;
      A ≟ carr AA,
      T ≟ ext_powerclass_setoid AA,
      R ≟ (mk_unary_morphism1 ?? (λX:𝛀^AA.
               mk_unary_morphism1 ?? (λY:𝛀^AA.
                  mk_ext_powerclass AA 
                    (ext_carr ? X ∩ ext_carr ? Y) 
                    (ext_prop AA (intersect_is_ext ? X Y)))
                (prop11 ?? (fun11 ?? (intersect_is_ext_morph AA) X))) 
              (prop11 ?? (intersect_is_ext_morph AA))) ,
       BB ≟ (ext_carr ? B),
       CC ≟ (ext_carr ? C)
   (* ---------------------------------------------------------------------------------------*) ⊢ 
      ext_carr AA (fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R B) C) ≡ intersect A BB CC.


(* hints for ∪ *)
nlemma union_is_morph : ∀A. Ω^A ⇒_1 (Ω^A ⇒_1 Ω^A).
#X; napply (mk_binary_morphism1 … (λA,B.A ∪ B));
#A1 A2 B1 B2 EA EB; napply ext_set; #x;
nchange in match (x ∈ (A1 ∪ B1)) with (?∨?);
napply (.= (set_ext ??? EA x)‡#);
napply (.= #‡(set_ext ??? EB x)); //;
nqed.

nlemma union_is_ext: ∀A. 𝛀^A → 𝛀^A → 𝛀^A.
 #S A B; @ (A ∪ B); #x y Exy; @; *; #H1; 
##[##1,3: @; ##|##*: @2 ]
##[##1,3: napply (. (Exy^-1)╪_1#) 
##|##2,4: napply (. Exy╪_1#)]
nassumption;
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, B,C :  𝛀^A;
   AA ≟ carr A,
   BB ≟ ext_carr ? B,
   CC ≟ ext_carr ? C,
   R ≟ mk_ext_powerclass ? 
         (ext_carr ? B ∪ ext_carr ? C) (ext_prop ? (union_is_ext ? B C))
(*-------------------------------------------------------------------------*)  ⊢
    ext_carr A R ≡ union AA BB CC.

unification hint 0 ≔ S:Type[0], A,B:Ω^S;
  T ≟ powerclass_setoid S,
  MM ≟ mk_unary_morphism1 ??
        (λA.mk_unary_morphism1 ?? 
          (λB.A ∪ B) (prop11 ?? (fun11 ?? (union_is_morph S) A)))
        (prop11 ?? (union_is_morph S))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T T (fun11 T (unary_morphism1_setoid1 T T) MM A) B ≡ A ∪ B.
   
nlemma union_is_ext_morph:∀A.𝛀^A ⇒_1 𝛀^A ⇒_1 𝛀^A.
#A; napply (mk_binary_morphism1 …  (union_is_ext …));
#x1 x2 y1 y2 Ex Ey; napply (prop11 … (union_is_morph A)); nassumption.
nqed.
            
unification hint 1 ≔
  AA : setoid, B,C : 𝛀^AA;
  A ≟ carr AA,
  T ≟ ext_powerclass_setoid AA,  
  R ≟ mk_unary_morphism1 ?? (λX:𝛀^AA.
           mk_unary_morphism1 ?? (λY:𝛀^AA.
              mk_ext_powerclass AA 
               (ext_carr ? X ∪ ext_carr ? Y) (ext_prop AA (union_is_ext ? X Y)))
            (prop11 ?? (fun11 ?? (union_is_ext_morph AA) X)))
          (prop11 ?? (union_is_ext_morph AA)),
   BB ≟ (ext_carr ? B),
   CC ≟ (ext_carr ? C)
(*------------------------------------------------------*) ⊢
   ext_carr AA (fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R B) C) ≡ union A BB CC.


(* hints for - *)
nlemma substract_is_morph : ∀A. Ω^A ⇒_1 (Ω^A ⇒_1 Ω^A).
#X; napply (mk_binary_morphism1 … (λA,B.A - B));
#A1 A2 B1 B2 EA EB; napply ext_set; #x;
nchange in match (x ∈ (A1 - B1)) with (?∧?);
napply (.= (set_ext ??? EA x)‡#); @; *; #H H1; @; //; #H2; napply H1;
##[ napply (. (set_ext ??? EB x)); ##| napply (. (set_ext ??? EB^-1 x)); ##] //;
nqed.

nlemma substract_is_ext: ∀A. 𝛀^A → 𝛀^A → 𝛀^A.
 #S A B; @ (A - B); #x y Exy; @; *; #H1 H2; @; ##[##2,4: #H3; napply H2]
##[##1,4: napply (. Exy╪_1#); // ##|##2,3: napply (. Exy^-1╪_1#); //]
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, B,C :  𝛀^A;
   AA ≟ carr A,
   BB ≟ ext_carr ? B,
   CC ≟ ext_carr ? C,
   R ≟ mk_ext_powerclass ? 
         (ext_carr ? B - ext_carr ? C) 
         (ext_prop ? (substract_is_ext ? B C))
(*---------------------------------------------------*)  ⊢
    ext_carr A R ≡ substract AA BB CC.

unification hint 0 ≔ S:Type[0], A,B:Ω^S;
  T ≟ powerclass_setoid S,  
  MM ≟ mk_unary_morphism1 ??
        (λA.mk_unary_morphism1 ?? 
          (λB.A - B) (prop11 ?? (fun11 ?? (substract_is_morph S) A)))
        (prop11 ?? (substract_is_morph S))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T T (fun11 T (unary_morphism1_setoid1 T T) MM A) B ≡ A - B.
   
nlemma substract_is_ext_morph:∀A.𝛀^A ⇒_1 𝛀^A ⇒_1 𝛀^A.
#A; napply (mk_binary_morphism1 …  (substract_is_ext …));
#x1 x2 y1 y2 Ex Ey; napply (prop11 … (substract_is_morph A)); nassumption.
nqed.
            
unification hint 1 ≔
  AA : setoid, B,C : 𝛀^AA;
  A ≟ carr AA,
  T ≟ ext_powerclass_setoid AA,    
  R ≟ mk_unary_morphism1 ?? (λX:𝛀^AA.
           mk_unary_morphism1 ?? (λY:𝛀^AA.
              mk_ext_powerclass AA 
                (ext_carr ? X - ext_carr ? Y) 
                (ext_prop AA (substract_is_ext ? X Y)))
            (prop11 ?? (fun11 ?? (substract_is_ext_morph AA) X)))
          (prop11 ?? (substract_is_ext_morph AA)),
   BB ≟ (ext_carr ? B),
   CC ≟ (ext_carr ? C)
(*------------------------------------------------------*) ⊢
   ext_carr AA (fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R B) C) ≡ substract A BB CC.

(* hints for {x} *)
nlemma single_is_morph : ∀A:setoid. (setoid1_of_setoid A) ⇒_1 Ω^A.
#X; @; ##[ napply (λx.{(x)}); ##] 
#a b E; napply ext_set; #x; @; #H; /3/; nqed.

nlemma single_is_ext: ∀A:setoid. A → 𝛀^A.
#X a; @; ##[ napply ({(a)}); ##] #x y E; @; #H; /3/; nqed. 

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ A : setoid, a : carr A;
   R ≟ (mk_ext_powerclass ? {(a)} (ext_prop ? (single_is_ext ? a)))
(*-------------------------------------------------------------------------*)  ⊢
    ext_carr A R ≡ singleton A a.

unification hint 0 ≔ A:setoid, a : carr A;
  T ≟ setoid1_of_setoid A,
  AA ≟ carr A,
  MM ≟ mk_unary_morphism1 ?? 
         (λa:carr1 (setoid1_of_setoid A).{(a)}) (prop11 ?? (single_is_morph A))
(*--------------------------------------------------------------------------*) ⊢
   fun11 T (powerclass_setoid AA) MM a ≡ {(a)}.
   
nlemma single_is_ext_morph:∀A:setoid.(setoid1_of_setoid A) ⇒_1 𝛀^A.
#A; @; ##[ #a; napply (single_is_ext ? a); ##] #a b E; @; #x; /3/; nqed.
            
unification hint 1 ≔ AA : setoid, a: carr AA;
  T ≟ ext_powerclass_setoid AA,
  R ≟ mk_unary_morphism1 ??
       (λa:carr1 (setoid1_of_setoid AA).
         mk_ext_powerclass AA {(a)} (ext_prop ? (single_is_ext AA a)))
            (prop11 ?? (single_is_ext_morph AA))
(*------------------------------------------------------*) ⊢
   ext_carr AA (fun11 (setoid1_of_setoid AA) T R a) ≡ singleton AA a.


(*
alias symbol "hint_decl" = "hint_decl_Type2".
unification hint 0 ≔
  A : setoid, B,C : 𝛀^A ;
  CC ≟ (ext_carr ? C),
  BB ≟ (ext_carr ? B),
  C1 ≟ (carr1 (powerclass_setoid (carr A))),
  C2 ≟ (carr1 (ext_powerclass_setoid A))
  ⊢ 
     eq_rel1 C1 (eq1 (powerclass_setoid (carr A))) BB CC ≡ 
          eq_rel1 C2 (eq1 (ext_powerclass_setoid A)) B C.
          
unification hint 0 ≔
  A, B : CPROP ⊢ iff A B ≡ eq_rel1 ? (eq1 CPROP) A B.    
    
nlemma test: ∀U.∀A,B:𝛀^U. A ∩ B = A →
 ∀x,y. x=y → x ∈ A → y ∈ A ∩ B.
 #U; #A; #B; #H; #x; #y; #K; #K2;
  alias symbol "prop2" = "prop21 mem".
  alias symbol "invert" = "setoid1 symmetry".
  napply (. K^-1‡H);
  nassumption;
nqed. 


nlemma intersect_ok: ∀A. binary_morphism1 (ext_powerclass_setoid A) (ext_powerclass_setoid A) (ext_powerclass_setoid A).
 #A; @
  [ #S; #S'; @
     [ napply (S ∩ S')
     | #a; #a'; #Ha;
        nwhd in ⊢ (? ? ? % %); @; *; #H1; #H2; @
        [##1,2: napply (. Ha^-1‡#); nassumption;
      ##|##3,4: napply (. Ha‡#); nassumption]##]
 ##| #a; #a'; #b; #b'; #Ha; #Hb; nwhd; @; #x; nwhd in ⊢ (% → %); #H
      [ alias symbol "invert" = "setoid1 symmetry".
        alias symbol "refl" = "refl".
alias symbol "prop2" = "prop21".
napply (. ((#‡Ha^-1)‡(#‡Hb^-1))); nassumption
      | napply (. ((#‡Ha)‡(#‡Hb))); nassumption ]##]
nqed.

(* unfold if intersect, exposing fun21 *)
alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ 
  A : setoid, B,C : ext_powerclass A ⊢ 
    pc A (fun21 …
            (mk_binary_morphism1 …
              (λS,S':qpowerclass_setoid A.mk_qpowerclass ? (S ∩ S') (mem_ok' ? (intersect_ok ? S S'))) 
              (prop21 … (intersect_ok A))) 
            B
            C) 
    ≡ intersect ? (pc ? B) (pc ? C).

nlemma test: ∀A:setoid. ∀U,V:qpowerclass A. ∀x,x':setoid1_of_setoid A. x=x' → x ∈ U ∩ V → x' ∈ U ∩ V.
 #A; #U; #V; #x; #x'; #H; #p; napply (. (H^-1‡#)); nassumption.
nqed.
*)

ndefinition image: ∀A,B. (carr A → carr B) → Ω^A → Ω^B ≝
 λA,B:setoid.λf:carr A → carr B.λSa:Ω^A.
  {y | ∃x. x ∈ Sa ∧ eq_rel (carr B) (eq0 B) (f x) y}.

ndefinition counter_image: ∀A,B. (carr A → carr B) → Ω^B → Ω^A ≝
 λA,B,f,Sb. {x | ∃y. y ∈ Sb ∧ f x = y}.

(******************* compatible equivalence relations **********************)

nrecord compatible_equivalence_relation (A: setoid) : Type[1] ≝
 { rel:> equivalence_relation A;
   compatibility: ∀x,x':A. x=x' → rel x x'
 }.

ndefinition quotient: ∀A. compatible_equivalence_relation A → setoid.
 #A; #R; @ A R; 
nqed.

(******************* first omomorphism theorem for sets **********************)

ndefinition eqrel_of_morphism:
 ∀A,B. A ⇒_0 B → compatible_equivalence_relation A.
 #A; #B; #f; @
  [ @ [ napply (λx,y. f x = f y) ] /2/;
##| #x; #x'; #H; nwhd; alias symbol "prop1" = "prop1".
napply (.= (†H)); // ]
nqed.

ndefinition canonical_proj: ∀A,R. A ⇒_0 (quotient A R).
 #A; #R; @
  [ napply (λx.x) |  #a; #a'; #H; napply (compatibility … R … H) ]
nqed.

ndefinition quotiented_mor:
 ∀A,B.∀f:A ⇒_0 B.(quotient … (eqrel_of_morphism … f)) ⇒_0 B.
 #A; #B; #f; @ [ napply f ] //.
nqed.

nlemma first_omomorphism_theorem_functions1:
 ∀A,B.∀f: unary_morphism A B.
  ∀x. f x = quotiented_mor … (canonical_proj … (eqrel_of_morphism … f) x).
//. nqed.

alias symbol "eq" = "setoid eq".
ndefinition surjective ≝
 λA,B.λS: ext_powerclass A.λT: ext_powerclass B.λf:A ⇒_0 B.
  ∀y. y ∈ T → ∃x. x ∈ S ∧ f x = y.

ndefinition injective ≝
 λA,B.λS: ext_powerclass A.λf:A ⇒_0 B.
  ∀x,x'. x ∈ S → x' ∈ S → f x = f x' → x = x'.

nlemma first_omomorphism_theorem_functions2:
 ∀A,B.∀f:A ⇒_0 B. 
   surjective … (Full_set ?) (Full_set ?) (canonical_proj ? (eqrel_of_morphism … f)).
/3/. nqed.

nlemma first_omomorphism_theorem_functions3:
 ∀A,B.∀f:A ⇒_0 B. 
   injective … (Full_set ?) (quotiented_mor … f).
 #A; #B; #f; nwhd; #x; #x'; #Hx; #Hx'; #K; nassumption.
nqed.

nrecord isomorphism (A, B : setoid) (S: ext_powerclass A) (T: ext_powerclass B) : Type[0] ≝
 { iso_f:> A ⇒_0 B;
   f_closed: ∀x. x ∈ S → iso_f x ∈ T;
   f_sur: surjective … S T iso_f;
   f_inj: injective … S iso_f
 }.


(*
nrecord isomorphism (A, B : setoid) (S: qpowerclass A) (T: qpowerclass B) : CProp[0] ≝
 { iso_f:> unary_morphism A B;
   f_closed: ∀x. x ∈ pc A S → fun1 ?? iso_f x ∈ pc B T}.
   
   
ncheck (λA:?.
   λB:?.
    λS:?.
     λT:?.
      λxxx:isomorphism A B S T.
       match xxx
       return λxxx:isomorphism A B S T.
               ∀x: carr A.
                ∀x_72: mem (carr A) (pc A S) x.
                 mem (carr B) (pc B T) (fun1 A B ((λ_.?) A B S T xxx) x)
        with [ mk_isomorphism _ yyy ⇒ yyy ] ).   
   
   ;
 }.
*)

(* Set theory *)

nlemma subseteq_intersection_l: ∀A.∀U,V,W:Ω^A.U ⊆ W ∨ V ⊆ W → U ∩ V ⊆ W.
#A; #U; #V; #W; *; #H; #x; *; /2/.
nqed.

nlemma subseteq_union_l: ∀A.∀U,V,W:Ω^A.U ⊆ W → V ⊆ W → U ∪ V ⊆ W.
#A; #U; #V; #W; #H; #H1; #x; *; /2/.
nqed.

nlemma subseteq_intersection_r: ∀A.∀U,V,W:Ω^A.W ⊆ U → W ⊆ V → W ⊆ U ∩ V.
/3/. nqed.

nlemma cupC : ∀S. ∀a,b:Ω^S.a ∪ b = b ∪ a.
#S a b; @; #w; *; nnormalize; /2/; nqed.

nlemma cupID : ∀S. ∀a:Ω^S.a ∪ a = a.
#S a; @; #w; ##[*; //] /2/; nqed.

(* XXX Bug notazione \cup, niente parentesi *)
nlemma cupA : ∀S.∀a,b,c:Ω^S.a ∪ b ∪ c = a ∪ (b ∪ c).
#S a b c; @; #w; *; /3/; *; /3/; nqed.

ndefinition Empty_set : ∀A.Ω^A ≝ λA.{ x | False }.

notation "∅" non associative with precedence 90 for @{ 'empty }.
interpretation "empty set" 'empty = (Empty_set ?).

nlemma cup0 :∀S.∀A:Ω^S.A ∪ ∅ = A.
#S p; @; #w; ##[*; //| #; @1; //] *; nqed.

