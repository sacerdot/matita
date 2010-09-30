(*
universe constraint Type[0] < Type[1].

ndefinition o ≝ Prop.
naxiom i : Type[0].

ninductive And (A,B:Prop) : Prop ≝ conj : A → B → And A B.
ninductive Exists (A : Type[0]) (P : A → Prop) : Prop ≝ exin : ∀a:A.P a → Exists A P.
ninductive Or (A,B:Prop) : Prop ≝ orl : A → Or A B | orr : B → Or A B.
ninductive True : Prop ≝ I : True.
ninductive False : Prop ≝ .
ninductive Not (A : Prop) : Prop ≝ abs : (A → False) → Not A.

ninductive Eq (a:i) : i → Prop ≝ refl : Eq a a.
ndefinition eq1 ≝ λT:Type[0].λp1,p2 : T → Prop. ∀x:T.And (p1 x → p2 x) (p2 x → p1 x).  

interpretation "eq" 'eq T A B = (Eq A B).
interpretation "exteq1" 'eq T A B = (eq1 T A B).

notation > "'Eq' term 90 A term 90 B" 
non associative with precedence 40 for @{'eq ? $A $B}.

interpretation "TPTP and" 'and A B = (And A B).
interpretation "TPTP not" 'not B = (Not B).
interpretation "TPTP ex"  'exists f = (Exists ? f).
*)
include "basics/eq.ma".

ndefinition o ≝ Prop.
naxiom i : Type[0].

interpretation "myeq" 'myeq T A B = (eq T A B).

notation > "'Eq' term 90 A term 90 B" 
non associative with precedence 40 for @{'myeq ? $A $B}.

naxiom bool_ext : ∀P,Q: o. (P → Q) → (Q → P) → P = Q.
naxiom f_ext_1 : ∀a,b:Type[0].∀f,g: a → b. (∀x.f x = g x) → f = g.
