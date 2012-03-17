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

include "basics/relations.ma".

(********** relations **********)

definition subR ≝ λA.λR,S:relation A.(∀a,b. R a b → S a b).

definition inv ≝ λA.λR:relation A.λa,b.R b a.

(* transitive closcure (plus) *)

inductive TC (A:Type[0]) (R:relation A) (a:A): A → Prop ≝
  |inj: ∀c. R a c → TC A R a c
  |step : ∀b,c.TC A R a b → R b c → TC A R a c.

theorem trans_TC: ∀A,R,a,b,c. 
  TC A R a b → TC A R b c → TC A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.

theorem TC_idem: ∀A,R. exteqR … (TC A R) (TC A (TC A R)).
#A #R #a #b % /2/ #H (elim H) /2/
qed.

lemma monotonic_TC: ∀A,R,S. subR A R S → subR A (TC A R) (TC A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_TC: ∀A,R,S. subR A R (TC A S) → subR A (TC A R) (TC A S).
#A #R #S #Hsub #a #b #H (elim H) /3/
qed.

theorem sub_TC_to_eq: ∀A,R,S. subR A R S → subR A S (TC A R) → 
  exteqR … (TC A R) (TC A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

theorem TC_inv: ∀A,R. exteqR ?? (TC A (inv A R)) (inv A (TC A R)).
#A #R #a #b %
#H (elim H) /2/ normalize #c #d #H1 #H2 #H3 @(trans_TC … H3) /2/
qed.
  
(* star *)
inductive star (A:Type[0]) (R:relation A) (a:A): A → Prop ≝
  |inj: ∀b,c.star A R a b → R b c → star A R a c
  |refl: star A R a a.

lemma R_to_star: ∀A,R,a,b. R a b → star A R a b.
#A #R #a #b /2/
qed.

theorem trans_star: ∀A,R,a,b,c. 
  star A R a b → star A R b c → star A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.

theorem star_star: ∀A,R. exteqR … (star A R) (star A (star A R)).
#A #R #a #b % /2/ #H (elim H) /2/
qed.

lemma monotonic_star: ∀A,R,S. subR A R S → subR A (star A R) (star A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_star: ∀A,R,S. subR A R (star A S) → 
  subR A (star A R) (star A S).
#A #R #S #Hsub #a #b #H (elim H) /3/
qed.

theorem sub_star_to_eq: ∀A,R,S. subR A R S → subR A S (star A R) → 
  exteqR … (star A R) (star A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

theorem star_inv: ∀A,R. 
  exteqR ?? (star A (inv A R)) (inv A (star A R)).
#A #R #a #b %
#H (elim H) /2/ normalize #c #d #H1 #H2 #H3 @(trans_star … H3) /2/
qed.

(* RC and star *)

lemma TC_to_star: ∀A,R,a,b.TC A R a b → star A R a b.
#R #A #a #b #TCH (elim TCH) /2/
qed.

lemma star_case: ∀A,R,a,b. star A R a b → a = b ∨ TC A R a b.
#A #R #a #b #H (elim H) /2/ #c #d #star_ac #Rcd * #H1 %2 /2/.
qed.

(* equiv -- smallest equivalence relation containing R *)

inductive equiv (A:Type[0]) (R:relation A) : A → A → Prop ≝
  |inje: ∀a,b,c.equiv A R a b → R b c → equiv A R a c
  |refle: ∀a,b.equiv A R a b
  |syme: ∀a,b.equiv A R a b → equiv A R b a.
  
theorem trans_equiv: ∀A,R,a,b,c. 
  equiv A R a b → equiv A R b c → equiv A R a c.
#A #R #a #b #c #Hab #Hbc (elim Hbc) /2/
qed.
 
theorem equiv_equiv: ∀A,R. exteqR … (equiv A R) (equiv A (equiv A R)).
#A #R #a #b % /2/  
qed.

lemma monotonic_equiv: ∀A,R,S. subR A R S → subR A (equiv A R) (equiv A S).
#A #R #S #subRS #a #b #H (elim H) /3/
qed.

lemma sub_equiv: ∀A,R,S. subR A R (equiv A S) → 
  subR A (equiv A R) (equiv A S).
#A #R #S #Hsub #a #b #H (elim H) /2/
qed.

theorem sub_equiv_to_eq: ∀A,R,S. subR A R S → subR A S (equiv A R) → 
  exteqR … (equiv A R) (equiv A S).
#A #R #S #sub1 #sub2 #a #b % /2/
qed.

(* well founded part of a relation *)

inductive WF (A:Type[0]) (R:relation A) : A → Prop ≝
  | wf : ∀b.(∀a. R a b → WF A R a) → WF A R b.

lemma WF_antimonotonic: ∀A,R,S. subR A R S → 
  ∀a. WF A S a → WF A R a.
#A #R #S #subRS #a #HWF (elim HWF) #b
#H #Hind % #c #Rcb @Hind @subRS //
qed.

(* added from lambda_delta *)

lemma TC_strap: ∀A. ∀R:relation A. ∀a1,a,a2.
                R a1 a → TC … R a a2 → TC … R a1 a2.
/3 width=3/ qed.

lemma TC_reflexive: ∀A,R. reflexive A R → reflexive A (TC … R).
/2 width=1/ qed.

lemma TC_star_ind: ∀A,R. reflexive A R → ∀a1. ∀P:predicate A.
                   P a1 → (∀a,a2. TC … R a1 a → R a a2 → P a → P a2) →
                   ∀a2. TC … R a1 a2 → P a2.
#A #R #H #a1 #P #Ha1 #IHa1 #a2 #Ha12 elim Ha12 -a2 /3 width=4/
qed.

inductive TC_dx (A:Type[0]) (R:relation A): A → A → Prop ≝
  |inj_dx: ∀a,c. R a c → TC_dx A R a c
  |step_dx : ∀a,b,c. R a b → TC_dx A R b c → TC_dx A R a c.

lemma TC_dx_strap: ∀A. ∀R: relation A.
                   ∀a,b,c. TC_dx A R a b → R b c → TC_dx A R a c.
#A #R #a #b #c #Hab elim Hab -a -b /3 width=3/
qed.

lemma TC_to_TC_dx: ∀A. ∀R: relation A.
                   ∀a1,a2. TC … R a1 a2 → TC_dx … R a1 a2.
#A #R #a1 #a2 #Ha12 elim Ha12 -a2 /2 width=3/
qed.

lemma TC_dx_to_TC: ∀A. ∀R: relation A.
                   ∀a1,a2. TC_dx … R a1 a2 → TC … R a1 a2.
#A #R #a1 #a2 #Ha12 elim Ha12 -a1 -a2 /2 width=3/
qed.

fact TC_star_ind_dx_aux: ∀A,R. reflexive A R →
                         ∀a2. ∀P:predicate A. P a2 →
                         (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                         ∀a1,a. TC … R a1 a → a = a2 → P a1.
#A #R #HR #a2 #P #Ha2 #H #a1 #a #Ha1
elim (TC_to_TC_dx ???? Ha1) -a1 -a
[ #a #c #Hac #H destruct /3 width=4/
| #a #b #c #Hab #Hbc #IH #H destruct /3 width=4/
]
qed-.

lemma TC_star_ind_dx: ∀A,R. reflexive A R →
                      ∀a2. ∀P:predicate A. P a2 →
                      (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                      ∀a1. TC … R a1 a2 → P a1.
#A #R #HR #a2 #P #Ha2 #H #a1 #Ha12
@(TC_star_ind_dx_aux … HR … Ha2 H … Ha12) //
qed-.

definition Conf3: ∀A. relation A → relation A → Prop ≝ λA,S,R.
                  ∀a,a1. S a1 a → ∀a2. R a1 a2 → S a2 a.

lemma TC_Conf3: ∀A,S,R. Conf3 A S R → Conf3 A S (TC … R).
#A #S #R #HSR #a #a1 #Ha1 #a2 #H elim H -a2 /2 width=3/
qed.
