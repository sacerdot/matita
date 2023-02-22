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

include "hints_declaration.ma".
include "sets/setoids1.ma".

ndefinition CPROP: setoid1.
 napply mk_setoid1
  [ napply CProp[0]
  | napply (mk_equivalence_relation1 CProp[0])
     [ napply iff
     | #x; napply mk_iff; #H; nassumption
     | #x; #y; *; #H1; #H2; napply mk_iff; nassumption
     | #x; #y; #z; *; #H1; #H2; *; #H3; #H4; napply mk_iff; #w
        [ napply (H3 (H1 w)) | napply (H2 (H4 w))]##]##]
nqed.

alias symbol "hint_decl" = "hint_decl_CProp2".
unification hint 0 ≔ ⊢ CProp[0] ≡ carr1 CPROP.

(*ndefinition CProp0_of_CPROP: carr1 CPROP → CProp[0] ≝ λx.x.
ncoercion CProp0_of_CPROP : ∀x: carr1 CPROP. CProp[0] ≝ CProp0_of_CPROP
 on _x: carr1 CPROP to CProp[0].*)

alias symbol "eq" = "setoid1 eq".

ndefinition fi': ∀A,B:CPROP. A = B → B → A.
 #A; #B; #H; napply (fi … H); nassumption.
nqed.

notation ". r" with precedence 55 for @{'fi $r}.
interpretation "fi" 'fi r = (fi' ?? r).

ndefinition and_morphism: unary_morphism1 CPROP (unary_morphism1_setoid1 CPROP CPROP).
 napply (mk_binary_morphism1 … And);
 #a; #a'; #b; #b'; #Ha; #Hb; @; *; #x; #y; @
  [ napply (. Ha^-1) | napply (. Hb^-1) | napply (. Ha) | napply (. Hb)] //.
nqed.

unification hint 0 ≔ A,B:CProp[0];
  T ≟ CPROP,
  MM ≟ mk_unary_morphism1 ??
       (λX.mk_unary_morphism1 ?? (And X) (prop11 ?? (fun11 ?? and_morphism X)))
         (prop11 ?? and_morphism)
(*-------------------------------------------------------------*) ⊢
  fun11 T T (fun11 T (unary_morphism1_setoid1 T T) MM A) B ≡ And A B.

(*
naxiom daemon: False.

nlemma test: ∀A,A',B: CProp[0]. A=A' → (B ∨ A) = B → (B ∧ A) ∧ B.
 #A; #A'; #B; #H1; #H2; napply (. (#‡H1)‡H2^-1); nelim daemon.
nqed.

CSC: ugly proof term
ncheck test.
*)

ndefinition or_morphism: unary_morphism1 CPROP (unary_morphism1_setoid1 CPROP CPROP).
 napply (mk_binary_morphism1 … Or);
 #a; #a'; #b; #b'; #Ha; #Hb; @; *; #x
  [ @1; napply (. Ha^-1) | @2; napply (. Hb^-1) | @1; napply (. Ha) | @2; napply (. Hb)] //.
nqed.

unification hint 0 ≔ A,B:CProp[0];
  T ≟ CPROP,
  MM ≟ mk_unary_morphism1 …
       (λX.mk_unary_morphism1 … (Or X) (prop11 … (fun11 ?? or_morphism X)))
         (prop11 … or_morphism)
(*-------------------------------------------------------------*) ⊢
  fun11 T T (fun11 T (unary_morphism1_setoid1 T T) MM A) B ≡ Or A B.
  
(* XXX always applied, generates hard unif problems  
ndefinition if_morphism: unary_morphism1 CPROP (unary_morphism1_setoid1 CPROP CPROP).
 napply (mk_binary_morphism1 … (λA,B:CProp[0]. A → B));
 #a; #a'; #b; #b'; #Ha; #Hb; @; #H; #x
  [ napply (. Hb^-1); napply H; napply (. Ha) | napply (. Hb); napply H; napply (. Ha^-1)]
 //.
nqed.

unification hint 0 ≔ A,B:CProp[0];
  T ≟ CPROP,
  R ≟ mk_unary_morphism1 …
       (λX:CProp[0].mk_unary_morphism1 … 
         (λY:CProp[0]. X → Y) (prop11 … (if_morphism X)))
         (prop11 … if_morphism)
(*----------------------------------------------------------------------*) ⊢
  fun11 T T (fun11 T (unary_morphism1_setoid1 T T) R A) B ≡ A → B.
*)

(* not as morphism *)
nlemma Not_morphism : CProp[0] ⇒_1 CProp[0].
@(λx:CProp[0].¬ x); #a b; *; #; @; /3/; nqed.

unification hint 0 ≔ P : CProp[0];
   A ≟ CPROP, 
   B ≟ CPROP,
   M ≟ mk_unary_morphism1 ?? (λP.¬ P) (prop11 ?? Not_morphism)
(*------------------------*)⊢
  fun11 A B M P ≡ ¬ P.

(* Ex setoid support *)

(* The caml, as some patches for it 
ncoercion setoid1_of_setoid : ∀s:setoid. setoid1 ≝ setoid1_of_setoid on _s: setoid to setoid1.
*)

(* simple case where the whole predicate can be rewritten *)
nlemma Ex_morphism : ∀S:setoid.((setoid1_of_setoid S) ⇒_1 CProp[0]) ⇒_1 CProp[0].
#S; @(λP: (setoid1_of_setoid S) ⇒_1 CProp[0].Ex S P); 
#P Q E; @; *; #x Px; @x; ncases (E x x #); /2/; nqed.

unification hint 0 ≔ S : setoid, P : (setoid1_of_setoid S) ⇒_1 CPROP;
   A ≟ unary_morphism1_setoid1 (setoid1_of_setoid S) CPROP, 
   B ≟ CPROP,
   M ≟ mk_unary_morphism1 ?? 
         (λP: (setoid1_of_setoid S) ⇒_1 CPROP.Ex (carr S) (fun11 ?? P)) 
         (prop11 ?? (Ex_morphism S))
(*------------------------*)⊢
  fun11 A B M P ≡ Ex (carr S) (fun11 (setoid1_of_setoid S) CPROP P).

nlemma Ex_morphism_eta : ∀S:setoid.((setoid1_of_setoid S) ⇒_1 CProp[0]) ⇒_1 CProp[0].
#S; @(λP: (setoid1_of_setoid S) ⇒_1 CProp[0].Ex S (λx.P x)); 
#P Q E; @; *; #x Px; @x; ncases (E x x #); /2/; nqed.

unification hint 0 ≔ S : setoid, P : (setoid1_of_setoid S) ⇒_1 CPROP;
   A ≟ unary_morphism1_setoid1 (setoid1_of_setoid S) CPROP, 
   B ≟ CPROP,
   M ≟ mk_unary_morphism1 ?? 
         (λP: (setoid1_of_setoid S) ⇒_1 CPROP.Ex (carr S) (λx.fun11 ?? P x)) 
         (prop11 ?? (Ex_morphism_eta S))
(*------------------------*)⊢
  fun11 A B M P ≡ Ex (carr S) (λx.fun11 (setoid1_of_setoid S) CPROP P x).

nlemma Ex_setoid : ∀S:setoid.((setoid1_of_setoid S) ⇒_1 CPROP) → setoid.
#T P; @ (Ex T (λx:T.P x)); @; ##[ #H1 H2; napply True |##*: //; ##] nqed.

unification hint 0 ≔ T : setoid,P ; 
   S ≟ (Ex_setoid T P) 
(*---------------------------*) ⊢
   Ex (carr T) (λx:carr T.fun11 ?? P x) ≡ carr S.

(* couts how many Ex we are traversing *)
ninductive counter : Type[0] ≝ 
 | End : counter 
 | Next : (Prop → Prop) → (* dummy arg please the notation mechanism *)
          counter → counter. 

(* to rewrite terms (live in setoid) *)
nlet rec mk_P (S, T : setoid) (n : counter) on n ≝ 
  match n with [ End ⇒ T → CProp[0] | Next _ m ⇒ S → (mk_P S T m) ].

nlet rec mk_F (S, T : setoid) (n : counter) on n ≝ 
  match n with [ End ⇒ T | Next _ m ⇒ S → (mk_F S T m) ].
  
nlet rec mk_E (S, T : setoid) (n : counter) on n : ∀f,g : mk_F S T n. CProp[0] ≝ 
  match n with 
  [ End ⇒ λf,g:T. f = g 
  | Next q m ⇒ λf,g: mk_F S T (Next q m). ∀x:S.mk_E S T m (f x) (g x) ].

nlet rec mk_H (S, T : setoid) (n : counter) on n : 
∀P1,P2: mk_P S T n.∀f,g : mk_F S T n. CProp[1] ≝ 
  match n with 
  [ End ⇒ λP1,P2:mk_P S T End.λf,g:T. f = g → P1 f =_1 P2 g 
  | Next q m ⇒ λP1,P2: mk_P S T (Next q m).λf,g: mk_F S T (Next q m). 
              ∀x:S.mk_H S T m (P1 x) (P2 x) (f x) (g x) ].

nlet rec mk_Ex (S, T : setoid) (n : counter) on n : 
∀P: mk_P S T n.∀f : mk_F S T n. CProp[0] ≝ 
  match n with 
  [ End ⇒ λP:mk_P S T End.λf:T. P f 
  | Next q m ⇒ λP: mk_P S T (Next q m).λf: mk_F S T (Next q m). 
              ∃x:S.mk_Ex S T m (P x) (f x) ].

nlemma Sig_generic : ∀S,T.∀n:counter.∀P,f,g.
  mk_E S T n f g → mk_H S T n P P f g → mk_Ex S T n P f =_1 mk_Ex S T n P g.
#S T n; nelim n; nnormalize;
##[ #P f g E H; /2/;
##| #q m IH P f g E H; @; *; #x Px; @x; ncases (IH … (E x) (H x)); /3/; ##]
nqed.

(* to rewrite propositions (live in setoid1) *)
nlet rec mk_P1 (S : setoid) (T : setoid1) (n : counter) on n ≝ 
  match n with [ End ⇒ T → CProp[0] | Next _ m ⇒ S → (mk_P1 S T m) ].

nlet rec mk_F1 (S : setoid) (T : setoid1) (n : counter) on n ≝ 
  match n with [ End ⇒ T | Next _ m ⇒ S → (mk_F1 S T m) ].
  
nlet rec mk_E1 (S : setoid) (T : setoid1) (n : counter) on n : ∀f,g : mk_F1 S T n. CProp[1] ≝ 
  match n with 
  [ End ⇒ λf,g:T. f =_1 g 
  | Next q m ⇒ λf,g: mk_F1 S T (Next q m). ∀x:S.mk_E1 S T m (f x) (g x) ].

nlet rec mk_H1 (S : setoid) (T : setoid1) (n : counter) on n : 
∀P1,P2: mk_P1 S T n.∀f,g : mk_F1 S T n. CProp[1] ≝ 
  match n with 
  [ End ⇒ λP1,P2:mk_P1 S T End.λf,g:T. f = g → P1 f =_1 P2 g 
  | Next q m ⇒ λP1,P2: mk_P1 S T (Next q m).λf,g: mk_F1 S T (Next q m). 
              ∀x:S.mk_H1 S T m (P1 x) (P2 x) (f x) (g x) ].

nlet rec mk_Ex1 (S : setoid) (T : setoid1) (n : counter) on n : 
∀P: mk_P1 S T n.∀f : mk_F1 S T n. CProp[0] ≝ 
  match n with 
  [ End ⇒ λP:mk_P1 S T End.λf:T. P f 
  | Next q m ⇒ λP: mk_P1 S T (Next q m).λf: mk_F1 S T (Next q m). 
              ∃x:S.mk_Ex1 S T m (P x) (f x) ].

nlemma Sig_generic1 : ∀S,T.∀n:counter.∀P,f,g.
  mk_E1 S T n f g → mk_H1 S T n P P f g → mk_Ex1 S T n P f =_1 mk_Ex1 S T n P g.
#S T n; nelim n; nnormalize;
##[ #P f g E H; /2/;
##| #q m IH P f g E H; @; *; #x Px; @x; ncases (IH … (E x) (H x)); /3/; ##]
nqed.

(* notation "∑x1,...,xn. E / H ; P" were:
   - x1...xn are bound in E and P, H is bound in P
   - H is an identifier that will have the type of E in P
   - P is the proof that the two existentially quantified predicates are equal*)
notation > "∑ list1 ident x sep , . term 61 E / ident nE ; term 19 H" with precedence 20 
for @{ 'Sig_gen 
  ${ fold right @{ 'End }  rec acc @{ ('Next (λ${ident x}.${ident x}) $acc) } }
  ${ fold right @{ $E }              rec acc @{ λ${ident x}.$acc } } 
  ${ fold right @{ λ${ident nE}.$H } rec acc @{ λ${ident x}.$acc } }
}.

interpretation "next" 'Next x y = (Next x y).
interpretation "end" 'End = End.
interpretation "sig_gen" 'Sig_gen n E H = (Sig_generic  ?? n ??? E H).
interpretation "sig_gen1" 'Sig_gen n E H = (Sig_generic1 ?? n ??? E H).

(*
nlemma test0 : ∀S:setoid. ∀P: (setoid1_of_setoid S) ⇒_1 CPROP.∀f,g:S → S.
 (∀x:S.f x = g x) → (Ex S (λw.P (f w))) =_1 (Ex S (λw.P (g w))).
#S P f g E; napply (∑w. E w / H ; ┼_1H); nqed.

nlemma test : ∀S:setoid. ∀P: (setoid1_of_setoid S) ⇒_1 CPROP.∀f,g:S → S.
 (∀x:S.f x = g x) → (Ex S (λw.P (f w)∧ True)) =_1 (Ex S (λw.P (g w)∧ True)).
#S P f g E; napply (∑w. E w / H ; (┼_1H)╪_1#); nqed. 

nlemma test_bound : ∀S:setoid. ∀e,f: (setoid1_of_setoid S) ⇒_1 CPROP. e = f → 
   (Ex S (λw.e w ∧ True)) =_1 (Ex S (λw.f w ∧ True)).
#S f g E; napply (.=_1 ∑x. E x x # / H ; (H ╪_1 #)); //; nqed.

nlemma test2 : ∀S:setoid. ∀ee: (setoid1_of_setoid S) ⇒_1 (setoid1_of_setoid S) ⇒_1 CPROP.
 ∀x,y:setoid1_of_setoid S.x =_1 y → 
   (True ∧ (Ex S (λw.ee x w ∧ True))) =_1 (True ∧ (Ex S (λw.ee y w ∧ True))).
#S m x y E; napply (.=_1 #╪_1(∑w. E / E ; ((E ╪_1 #) ╪_1 #))). //; nqed.

nlemma test3 : ∀S:setoid. ∀ee: (setoid1_of_setoid S) ⇒_1 (setoid1_of_setoid S) ⇒_1 CPROP.
 ∀x,y:setoid1_of_setoid S.x =_1 y → 
   ((Ex S (λw.ee x w ∧ True) ∨ True)) =_1 ((Ex S (λw.ee y w ∧ True) ∨ True)).
#S m x y E; napply (.=_1 (∑w. E / E ; ((E ╪_1 #) ╪_1 #)) ╪_1 #). //; nqed.
*)
  
