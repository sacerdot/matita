(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/logic.ma".

(********** predicates *********)

definition predicate: Type[0] → Type[0]
≝ λA.A→Prop.

(********** relations **********)
definition relation : Type[0] → Type[0]
≝ λA.A→A→Prop. 

definition relation2 : Type[0] → Type[0] → Type[0]
≝ λA,B.A→B→Prop.

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

(********** operations **********)
definition Rcomp ≝ λA.λR1,R2:relation A.λa1,a2.
  ∃am.R1 a1 am ∧ R2 am a2.
interpretation "relation composition" 'compose R1 R2 = (Rcomp ? R1 R2).

definition Runion ≝ λA.λR1,R2:relation A.λa,b. R1 a b ∨ R2 a b.
interpretation "union of relations" 'union R1 R2 = (Runion ? R1 R2).
    
definition Rintersection ≝ λA.λR1,R2:relation A.λa,b.R1 a b ∧ R2 a b.
interpretation "interesecion of relations" 'intersects R1 R2 = (Rintersection ? R1 R2).

definition inv ≝ λA.λR:relation A.λa,b.R b a.

(*********** sub relation ***********)
definition subR ≝ λA.λR,S:relation A.(∀a,b. R a b → S a b).
interpretation "relation inclusion" 'subseteq R S = (subR ? R S).

lemma sub_reflexive : 
  ∀T.∀R:relation T.R ⊆ R.
#T #R #x //
qed.

lemma sub_comp_l:  ∀A.∀R,R1,R2:relation A.
  R1 ⊆ R2 → R1 ∘ R ⊆ R2 ∘ R.
#A #R #R1 #R2 #Hsub #a #b * #c * /4/
qed.

lemma sub_comp_r:  ∀A.∀R,R1,R2:relation A.
  R1 ⊆ R2 → R ∘ R1 ⊆ R ∘ R2.
#A #R #R1 #R2 #Hsub #a #b * #c * /4/
qed.

lemma sub_assoc_l: ∀A.∀R1,R2,R3:relation A.
  R1 ∘ (R2 ∘ R3) ⊆ (R1 ∘ R2) ∘ R3.
#A #R1 #R2 #R3 #a #b * #c * #Hac * #d * /5/
qed.

lemma sub_assoc_r: ∀A.∀R1,R2,R3:relation A.
  (R1 ∘ R2) ∘ R3 ⊆ R1 ∘ (R2 ∘ R3).
#A #R1 #R2 #R3 #a #b * #c * * #d * /5 width=5/ 
qed.

(************* functions ************)

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

lemma injective_compose : ∀A,B,C,f,g.
injective A B f → injective B C g → injective A C (λx.g (f x)).
/3/; qed-.

(* extensional equality *)

(* moved inside sets.ma
definition exteqP: ∀A:Type[0].∀P,Q:A→Prop.Prop ≝
λA.λP,Q.∀a.iff (P a) (Q a). *)

definition exteqR: ∀A,B:Type[0].∀R,S:A→B→Prop.Prop ≝
λA,B.λR,S.∀a.∀b.iff (R a b) (S a b).

definition exteqF: ∀A,B:Type[0].∀f,g:A→B.Prop ≝
λA,B.λf,g.∀a.f a = g a.

(*
notation " x \eqP y " non associative with precedence 45 
for @{'eqP A $x $y}.

interpretation "functional extentional equality" 
'eqP A x y = (exteqP A x y). *)

notation "x \eqR y" non associative with precedence 45 
for @{'eqR ? ? x y}.

interpretation "functional extentional equality" 
'eqR A B R S = (exteqR A B R S).

notation " f \eqF g " non associative with precedence 45
for @{'eqF ? ? f g}.

interpretation "functional extentional equality" 
'eqF A B f g = (exteqF A B f g).

(********** relations on unboxed pairs **********)

definition bi_relation: Type[0] → Type[0] → Type[0]
≝ λA,B.A→B→A→B→Prop.

definition bi_reflexive: ∀A,B. ∀R :bi_relation A B. Prop
≝ λA,B,R. ∀x,y. R x y x y.
