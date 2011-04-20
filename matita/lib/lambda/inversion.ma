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

include "lambda/types.ma".

(*
inductive TJ: list T → T → T → Prop ≝
  | ax : ∀i,j. A i j → TJ (nil T) (Sort i) (Sort j)
  | start: ∀G.∀A.∀i.TJ G A (Sort i) → TJ (A::G) (Rel 0) (lift A 0 1)
  | weak: ∀G.∀A,B,C.∀i.
     TJ G A B → TJ G C (Sort i) → TJ (C::G) (lift A 0 1) (lift B 0 1)
  | prod: ∀G.∀A,B.∀i,j,k. R i j k →
     TJ G A (Sort i) → TJ (A::G) B (Sort j) → TJ G (Prod A B) (Sort k)
  | app: ∀G.∀F,A,B,a. 
     TJ G F (Prod A B) → TJ G a A → TJ G (App F a) (subst B 0 a)
  | abs: ∀G.∀A,B,b.∀i. 
     TJ (A::G) b B → TJ G (Prod A B) (Sort i) → TJ G (Lambda A b) (Prod A B)
  | conv: ∀G.∀A,B,C.∀i. conv B C →
     TJ G A B → TJ G C (Sort i) → TJ G A C
  | dummy: ∀G.∀A,B.∀i. 
     TJ G A B → TJ G B (Sort i) → TJ G (D A) B.
     axiom prod_inv : ∀G,M,P,Q. G ⊢ M : Prod P Q →
 ∃i. P::G ⊢ Q : Sort i. *)

axiom lambda_lift : ∀A,B,C. lift A 0 1 = Lambda B C →
∃P,Q. A = Lambda P Q ∧ lift P 0 1  = B ∧ lift Q 1 1 = C.

axiom prod_lift : ∀A,B,C. lift A 0 1 = Prod B C →
∃P,Q. A = Prod P Q ∧ lift P 0 1  = B ∧ lift Q 1 1 = C.

axiom conv_lift: ∀M,N. conv M N → conv (lift M 0 1) (lift N 0 1).
 
axiom weak_in: ∀G.∀A,B,M,N.∀i.A::G  ⊢ M : N → G ⊢ B : Sort i → 
 (lift A 0 1)::B::G ⊢  lift M 1 1 : lift N 1 1.

axiom refl_conv: ∀A. conv A A.
axiom  sym_conv: ∀A,B. conv A B → conv B A.
axiom trans_conv: ∀A,B,C. conv A B → conv B C → conv A C.

theorem prod_inv: ∀G,M,N. G ⊢ M : N → ∀A,B.M = Prod A B → 
  ∃i,j,k. conv N (Sort k) ∧ G ⊢A : Sort i ∧ A::G ⊢B : Sort j. 
#G #M #N #t (elim t);
  [#i #j #Aij #A #b #H destruct
  |#G1 #P #i #t #_ #A #b #H destruct
  |#G1 #P #Q #R #i #t1 #t2 #H1 #_ #A #B #Hl
   cases (prod_lift … Hl) #A1 * #B1 * * #eqP #eqA #eqB
   cases (H1 … eqP) #i * #j * #k * * #c1 #t3 #t4
   @(ex_intro … i) @(ex_intro … j) @(ex_intro … k) <eqA <eqB %
    [% [@(conv_lift … c1) |@(weak … t3 t2)]
    |@(weak_in … t4 t2) 
    ]
  |#G1 #A #B #i #j #k #Rijk #t1 #t2 #_ #_ #A1 #B1 #H destruct
   @(ex_intro … i) @(ex_intro … j) @(ex_intro … k) % // % //
  |#G1 #P #A #B #C #t1 #t2 #_ #_ #A1 #B1 #H destruct
  |#G1 #P #A #B #i #t1 #t2 #_ #_ #A1 #B1 #H destruct
  |#G1 #A #B #C #i #cBC #t1 #t2 #H1 #H2 #A1 #B1 #eqA
   cases (H1 … eqA) #i * #j * #k * * #c1 #t3 #t4
   @(ex_intro … i) @(ex_intro … j) @(ex_intro … k) % //
   % // @(trans_conv C B … c1) @sym_conv //
  |#G1 #A #B #i #t1 #t2 #_ #_ #A1 #B1 #eqA destruct
  ]
qed.

theorem abs_inv: ∀G,M,N. G ⊢ M : N → ∀A,b.M = Lambda A b → 
  ∃i,B. conv N (Prod A B) ∧ G ⊢Prod A B: Sort i ∧ A::G ⊢b : B. 
#G #M #N #t (elim t);
  [#i #j #Aij #A #b #H destruct
  |#G1 #P #i #t #_ #A #b #H destruct
  |#G1 #P #Q #R #i #t1 #t2 #H1 #_ #A #b #Hl
   cases (lambda_lift … Hl) #A1 * #b1 * * #eqP #eqA #eqb
   cases (H1 … eqP) #i * #B1 * * #c1 #t3 #t4
   @(ex_intro … i) @(ex_intro … (lift B1 1 1)) <eqA <eqb %
    [% [@(conv_lift … c1) |@(weak … t3 t2)]
    |@(weak_in … t4 t2) 
    ]
  |#G1 #A #B #i #j #k #Rijk #t1 #t2 #_ #_ #A1 #b #H destruct
  |#G1 #P #A #B #C #t1 #t2 #_ #_ #A1 #b #H destruct
  |#G1 #P #A #B #i #t1 #t2 #_ #_ #A1 #b #H destruct
    @(ex_intro … i) @(ex_intro … A) % // % //
  |#G1 #A #B #C #i #cBC #t1 #t2 #H1 #H2 #A1 #b #eqA
   cases (H1 … eqA) #i * #B1 * * #c1 #t3 #t4
   @(ex_intro … i) @(ex_intro … B1) % //
   % // @(trans_conv C B … c1) @sym_conv //
  |#G1 #A #B #i #t1 #t2 #_ #_ #A1 #b #eqA destruct
  ]
qed.
   
