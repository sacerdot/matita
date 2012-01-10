include "basics/logic.ma".

(********** relations **********)
definition relation : Type[0] → Type[0]
≝ λA.A→A→Prop. 

definition reflexive: ∀A.∀R :relation A.Prop
≝ λA.λR.∀x:A.R x x.

definition symmetric: ∀A.∀R: relation A.Prop
≝ λA.λR.∀x,y:A.R x y → R y x.

definition transitive: ∀A.∀R:relation A.Prop
≝ λA.λR.∀x,y,z:A.R x y → R y z → R x z.

definition irreflexive: ∀A.∀R:relation A.Prop
≝ λA.λR.∀x:A.¬(R x x).

definition cotransitive: ∀A.∀R:relation A.Prop
≝ λA.λR.∀x,y:A.R x y → ∀z:A. R x z ∨ R z y.

definition tight_apart: ∀A.∀eq,ap:relation A.Prop
≝ λA.λeq,ap.∀x,y:A. (¬(ap x y) → eq x y) ∧
(eq x y → ¬(ap x y)).

definition antisymmetric: ∀A.∀R:relation A.Prop
≝ λA.λR.∀x,y:A. R x y → ¬(R y x).

(********** functions **********)

definition compose ≝
  λA,B,C:Type[0].λf:B→C.λg:A→B.λx:A.f (g x).

interpretation "function composition" 'compose f g = (compose ? ? ? f g).

definition injective: ∀A,B:Type[0].∀ f:A→B.Prop
≝ λA,B.λf.∀x,y:A.f x = f y → x=y.

definition surjective: ∀A,B:Type[0].∀f:A→B.Prop
≝λA,B.λf.∀z:B.∃x:A.z = f x.

definition commutative: ∀A:Type[0].∀f:A→A→A.Prop 
≝ λA.λf.∀x,y.f x y = f y x.

definition commutative2: ∀A,B:Type[0].∀f:A→A→B.Prop
≝ λA,B.λf.∀x,y.f x y = f y x.

definition associative: ∀A:Type[0].∀f:A→A→A.Prop
≝ λA.λf.∀x,y,z.f (f x y) z = f x (f y z).

(* functions and relations *)
definition monotonic : ∀A:Type[0].∀R:A→A→Prop.
∀f:A→A.Prop ≝
λA.λR.λf.∀x,y:A.R x y → R (f x) (f y).

(* functions and functions *)
definition distributive: ∀A:Type[0].∀f,g:A→A→A.Prop
≝ λA.λf,g.∀x,y,z:A. f x (g y z) = g (f x y) (f x z).

definition distributive2: ∀A,B:Type[0].∀f:A→B→B.∀g:B→B→B.Prop
≝ λA,B.λf,g.∀x:A.∀y,z:B. f x (g y z) = g (f x y) (f x z).

(* extensional equality *)

definition exteqR: ∀A,B:Type[0].∀R,S:A→B→Prop.Prop ≝
λA,B.λR,S.∀a.∀b.iff (R a b) (S a b).

definition exteqF: ∀A,B:Type[0].∀f,g:A→B.Prop ≝
λA,B.λf,g.∀a.f a = g a.

notation "x \eqR y" non associative with precedence 45 
for @{'eqR ? ? x y}.

interpretation "functional extentional equality" 
'eqR A B R S = (exteqR A B R S).

notation " f \eqF g " non associative with precedence 45
for @{'eqF ? ? f g}.

interpretation "functional extentional equality" 
'eqF A B f g = (exteqF A B f g).

