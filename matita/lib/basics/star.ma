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
  |sstep: ∀b,c.star A R a b → R b c → star A R a c
  |srefl: star A R a a.

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

lemma star_decomp_l : 
  ∀A,R,x,y.star A R x y → x = y ∨ ∃z.R x z ∧ star A R z y.
#A #R #x #y #Hstar elim Hstar
[ #b #c #Hleft #Hright *
  [ #H1 %2 @(ex_intro ?? c) % //
  | * #x0 * #H1 #H2 %2 @(ex_intro ?? x0) % /2/ ]
| /2/ ]
qed.

(* right associative version of star *)
inductive starl (A:Type[0]) (R:relation A) : A → A → Prop ≝
  |sstepl: ∀a,b,c.R a b → starl A R b c → starl A R a c
  |refll: ∀a.starl A R a a.
 
lemma starl_comp : ∀A,R,a,b,c.
  starl A R a b → R b c → starl A R a c.
#A #R #a #b #c #Hstar elim Hstar 
  [#a1 #b1 #c1 #Rab #sbc #Hind #a1 @(sstepl … Rab) @Hind //
  |#a1 #Rac @(sstepl … Rac) //
  ]
qed.

lemma star_compl : ∀A,R,a,b,c.
  R a b → star A R b c → star A R a c.
#A #R #a #b #c #Rab #Hstar elim Hstar 
  [#b1 #c1 #sbb1 #Rb1c1 #Hind @(sstep … Rb1c1) @Hind
  |@(sstep … Rab) //
  ]
qed.

lemma star_to_starl: ∀A,R,a,b.star A R a b → starl A R a b.
#A #R #a #b #Hs elim Hs //
#d #c #sad #Rdc #sad @(starl_comp … Rdc) //
qed.

lemma starl_to_star: ∀A,R,a,b.starl A R a b → star A R a b.
#A #R #a #b #Hs elim Hs // -Hs -b -a
#a #b #c #Rab #sbc #sbc @(star_compl … Rab) //
qed.

fact star_ind_l_aux: ∀A,R,a2. ∀P:predicate A.
                     P a2 →
                     (∀a1,a. R a1 a → star … R a a2 → P a → P a1) →
                     ∀a1,a. star … R a1 a → a = a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #a #Ha1
elim (star_to_starl ???? Ha1) -a1 -a
[ #a #b #c #Hab #Hbc #IH #H destruct /3 width=4/
| #a #H destruct /2 width=1/
]
qed-.

(* imporeved version of star_ind_l with "left_parameter" *)
lemma star_ind_l: ∀A,R,a2. ∀P:predicate A.
                  P a2 →
                  (∀a1,a. R a1 a → star … R a a2 → P a → P a1) →
                  ∀a1. star … R a1 a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #Ha12
@(star_ind_l_aux … H1 H2 … Ha12) //
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
qed-.

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

fact TC_ind_dx_aux: ∀A,R,a2. ∀P:predicate A.
                    (∀a1. R a1 a2 → P a1) →
                    (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                    ∀a1,a. TC … R a1 a → a = a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #a #Ha1
elim (TC_to_TC_dx ???? Ha1) -a1 -a
[ #a #c #Hac #H destruct /2 width=1/
| #a #b #c #Hab #Hbc #IH #H destruct /3 width=4/
]
qed-.

lemma TC_ind_dx: ∀A,R,a2. ∀P:predicate A.
                 (∀a1. R a1 a2 → P a1) →
                 (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                 ∀a1. TC … R a1 a2 → P a1.
#A #R #a2 #P #H1 #H2 #a1 #Ha12
@(TC_ind_dx_aux … H1 H2 … Ha12) //
qed-.

lemma TC_symmetric: ∀A,R. symmetric A R → symmetric A (TC … R).
#A #R #HR #x #y #H @(TC_ind_dx ??????? H) -x /3 width=1/ /3 width=3/
qed.

lemma TC_star_ind_dx: ∀A,R. reflexive A R →
                      ∀a2. ∀P:predicate A. P a2 →
                      (∀a1,a. R a1 a → TC … R a a2 → P a → P a1) →
                      ∀a1. TC … R a1 a2 → P a1.
#A #R #HR #a2 #P #Ha2 #H #a1 #Ha12
@(TC_ind_dx … P ? H … Ha12) /3 width=4/
qed-.

definition Conf3: ∀A,B. relation2 A B → relation A → Prop ≝ λA,B,S,R.
                  ∀b,a1. S a1 b → ∀a2. R a1 a2 → S a2 b.

lemma TC_Conf3: ∀A,B,S,R. Conf3 A B S R → Conf3 A B S (TC … R).
#A #B #S #R #HSR #b #a1 #Ha1 #a2 #H elim H -a2 /2 width=3/
qed.

inductive bi_TC (A,B:Type[0]) (R:bi_relation A B) (a:A) (b:B): relation2 A B ≝
  |bi_inj : ∀c,d. R a b c d → bi_TC A B R a b c d
  |bi_step: ∀c,d,e,f. bi_TC A B R a b c d → R c d e f → bi_TC A B R a b e f.

lemma bi_TC_strap: ∀A,B. ∀R:bi_relation A B. ∀a1,a,a2,b1,b,b2.
                   R a1 b1 a b → bi_TC … R a b a2 b2 → bi_TC … R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #HR #H elim H -a2 -b2 /2 width=4/ /3 width=4/
qed.

lemma bi_TC_reflexive: ∀A,B,R. bi_reflexive A B R →
                       bi_reflexive A B (bi_TC … R).
/2 width=1/ qed.

inductive bi_TC_dx (A,B:Type[0]) (R:bi_relation A B): bi_relation A B ≝
  |bi_inj_dx  : ∀a1,a2,b1,b2. R a1 b1 a2 b2 → bi_TC_dx A B R a1 b1 a2 b2
  |bi_step_dx : ∀a1,a,a2,b1,b,b2. R a1 b1 a b → bi_TC_dx A B R a b a2 b2 →
                bi_TC_dx A B R a1 b1 a2 b2.

lemma bi_TC_dx_strap: ∀A,B. ∀R: bi_relation A B.
                      ∀a1,a,a2,b1,b,b2. bi_TC_dx A B R a1 b1 a b →
                      R a b a2 b2 → bi_TC_dx A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H1 elim H1 -a -b /3 width=4/
qed.

lemma bi_TC_to_bi_TC_dx: ∀A,B. ∀R: bi_relation A B.
                         ∀a1,a2,b1,b2. bi_TC … R a1 b1 a2 b2 →
                         bi_TC_dx … R a1 b1 a2 b2.
#A #B #R #a1 #a2 #b1 #b2 #H12 elim H12 -a2 -b2 /2 width=4/
qed.

lemma bi_TC_dx_to_bi_TC: ∀A,B. ∀R: bi_relation A B.
                         ∀a1,a2,b1,b2. bi_TC_dx … R a1 b1 a2 b2 →
                         bi_TC … R a1 b1 a2 b2.
#A #b #R #a1 #a2 #b1 #b2 #H12 elim H12 -a1 -a2 -b1 -b2 /2 width=4/
qed.

fact bi_TC_ind_dx_aux: ∀A,B,R,a2,b2. ∀P:relation2 A B.
                       (∀a1,b1. R a1 b1 a2 b2 → P a1 b1) →
                       (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                       ∀a1,a,b1,b. bi_TC … R a1 b1 a b → a = a2 → b = b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H1 #H2 #a1 #a #b1 #b #H1
elim (bi_TC_to_bi_TC_dx ??????? H1) -a1 -a -b1 -b
[ #a1 #x #b1 #y #H1 #Hx #Hy destruct /2 width=1/
| #a1 #a #x #b1 #b #y #H1 #H #IH #Hx #Hy destruct /3 width=5/
]
qed-.

lemma bi_TC_ind_dx: ∀A,B,R,a2,b2. ∀P:relation2 A B.
                    (∀a1,b1. R a1 b1 a2 b2 → P a1 b1) →
                    (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                    ∀a1,b1. bi_TC … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H1 #H2 #a1 #b1 #H12
@(bi_TC_ind_dx_aux ?????? H1 H2 … H12) //
qed-.

lemma bi_TC_symmetric: ∀A,B,R. bi_symmetric A B R →
                       bi_symmetric A B (bi_TC … R).
#A #B #R #HR #a1 #a2 #b1 #b2 #H21
@(bi_TC_ind_dx ?????????? H21) -a2 -b2 /3 width=1/ /3 width=4/
qed.

lemma bi_TC_transitive: ∀A,B,R. bi_transitive A B (bi_TC … R).
#A #B #R #a1 #a #b1 #b #H elim H -a -b /2 width=4/ /3 width=4/
qed.

definition bi_Conf3: ∀A,B,C. relation3 A B C → bi_relation A B → Prop ≝ λA,B,C,S,R.
                     ∀c,a1,b1. S a1 b1 c → ∀a2,b2. R a1 b1 a2 b2 → S a2 b2 c.

lemma bi_TC_Conf3: ∀A,B,C,S,R. bi_Conf3 A B C S R → bi_Conf3 A B C S (bi_TC … R).
#A #B #C #S #R #HSR #c #a1 #b1 #Hab1 #a2 #b2 #H elim H -a2 -b2 /2 width=4/
qed.

lemma bi_TC_star_ind: ∀A,B,R. bi_reflexive A B R → ∀a1,b1. ∀P:relation2 A B.
                      P a1 b1 → (∀a,a2,b,b2. bi_TC … R a1 b1 a b → R a b a2 b2 → P a b → P a2 b2) →
                      ∀a2,b2. bi_TC … R a1 b1 a2 b2 → P a2 b2.
#A #B #R #HR #a1 #b1 #P #H1 #IH #a2 #b2 #H12 elim H12 -a2 -b2 /3 width=5/
qed-.

lemma bi_TC_star_ind_dx: ∀A,B,R. bi_reflexive A B R →
                         ∀a2,b2. ∀P:relation2 A B. P a2 b2 →
                         (∀a1,a,b1,b. R a1 b1 a b → bi_TC … R a b a2 b2 → P a b → P a1 b1) →
                         ∀a1,b1. bi_TC … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #HR #a2 #b2 #P #H2 #IH #a1 #b1 #H12
@(bi_TC_ind_dx … P ? IH … H12) /3 width=5/
qed-.

definition bi_star: ∀A,B,R. bi_relation A B ≝ λA,B,R,a1,b1,a2,b2.
                    (a1 = a2 ∧ b1 = b2) ∨ bi_TC A B R a1 b1 a2 b2.

lemma bi_star_bi_reflexive: ∀A,B,R. bi_reflexive A B (bi_star … R).
/3 width=1/ qed.

lemma bi_TC_to_bi_star: ∀A,B,R,a1,b1,a2,b2.
                        bi_TC A B R a1 b1 a2 b2 → bi_star A B R a1 b1 a2 b2.
/2 width=1/ qed.

lemma bi_R_to_bi_star: ∀A,B,R,a1,b1,a2,b2.
                       R a1 b1 a2 b2 → bi_star A B R a1 b1 a2 b2.
/3 width=1/ qed.

lemma bi_star_strap1: ∀A,B,R,a1,a,a2,b1,b,b2. bi_star A B R a1 b1 a b →
                      R a b a2 b2 → bi_star A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 *
[ * #H1 #H2 destruct /2 width=1/
| /3 width=4/
]
qed.

lemma bi_star_strap2: ∀A,B,R,a1,a,a2,b1,b,b2. R a1 b1 a b →
                      bi_star A B R a b a2 b2 → bi_star A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H *
[ * #H1 #H2 destruct /2 width=1/
| /3 width=4/
]
qed.

lemma bi_star_to_bi_TC_to_bi_TC: ∀A,B,R,a1,a,a2,b1,b,b2. bi_star A B R a1 b1 a b →
                                 bi_TC A B R a b a2 b2 → bi_TC A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 *
[ * #H1 #H2 destruct /2 width=1/
| /2 width=4/
]
qed.

lemma bi_TC_to_bi_star_to_bi_TC: ∀A,B,R,a1,a,a2,b1,b,b2. bi_TC A B R a1 b1 a b →
                                 bi_star A B R a b a2 b2 → bi_TC A B R a1 b1 a2 b2.
#A #B #R #a1 #a #a2 #b1 #b #b2 #H *
[ * #H1 #H2 destruct /2 width=1/
| /2 width=4/
]
qed.

lemma bi_tansitive_bi_star: ∀A,B,R. bi_transitive A B (bi_star … R).
#A #B #R #a1 #a #b1 #b #H #a2 #b2 *
[ * #H1 #H2 destruct /2 width=1/
| /3 width=4/
]
qed.

lemma bi_star_ind: ∀A,B,R,a1,b1. ∀P:relation2 A B. P a1 b1 →
                   (∀a,a2,b,b2. bi_star … R a1 b1 a b → R a b a2 b2 → P a b → P a2 b2) →
                   ∀a2,b2. bi_star … R a1 b1 a2 b2 → P a2 b2.
#A #B #R #a1 #b1 #P #H #IH #a2 #b2 *
[ * #H1 #H2 destruct //
| #H12 elim H12 -a2 -b2 /2 width=5/ -H /3 width=5/
]
qed-.

lemma bi_star_ind_dx: ∀A,B,R,a2,b2. ∀P:relation2 A B. P a2 b2 →
                      (∀a1,a,b1,b. R a1 b1 a b → bi_star … R a b a2 b2 → P a b → P a1 b1) →
                      ∀a1,b1. bi_star … R a1 b1 a2 b2 → P a1 b1.
#A #B #R #a2 #b2 #P #H #IH #a1 #b1 *
[ * #H1 #H2 destruct //
| #H12 @(bi_TC_ind_dx ?????????? H12) -a1 -b1 /2 width=5/ -H /3 width=5/
]
qed-.
