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

include "lambda/par_reduction.ma".
include "basics/star.ma".

(*
inductive T : Type[0] ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
  | D: T →T
. *)

inductive red : T →T → Prop ≝
  | rbeta: ∀P,M,N. red (App (Lambda P M) N) (M[0 ≝ N])
  | rdapp: ∀M,N. red (App (D M) N) (D (App M N))
  | rdlam: ∀M,N. red (Lambda M (D N)) (D (Lambda M N))
  | rappl: ∀M,M1,N. red M M1 → red (App M N) (App M1 N)
  | rappr: ∀M,N,N1. red N N1 → red (App M N) (App M N1)
  | rlaml: ∀M,M1,N. red M M1 → red (Lambda M N) (Lambda M1 N)
  | rlamr: ∀M,N,N1. red N N1 → red(Lambda M N) (Lambda M N1)
  | rprodl: ∀M,M1,N. red M M1 → red (Prod M N) (Prod M1 N)
  | rprodr: ∀M,N,N1. red N N1 → red (Prod M N) (Prod M N1)
  | d: ∀M,M1. red M M1 → red (D M) (D M1).

lemma red_to_pr: ∀M,N. red M N → pr M N.
#M #N #redMN (elim redMN) /2/
qed.

lemma red_d : ∀M,P. red (D M) P → ∃N. P = D N ∧ red M N.
#M #P #redMP (inversion redMP)
  [#P1 #M1 #N1 #eqH destruct
  |#M1 #N1 #eqH destruct
  |#M1 #N1 #eqH destruct 
  |4,5,6,7,8,9:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #red1 #_ #eqH destruct #eqP @(ex_intro … M1) /2/
  ]
qed.

lemma red_lambda : ∀M,N,P. red (Lambda M N) P →
 (∃M1. P = (Lambda M1 N) ∧ red M M1) ∨
 (∃N1. P = (Lambda M N1) ∧ red N N1) ∨
 (∃Q. N = D Q ∧ P = D (Lambda M Q)).
#M #N #P #redMNP (inversion redMNP)
  [#P1 #M1 #N1 #eqH destruct
  |#M1 #N1 #eqH destruct
  |#M1 #N1 #eqH destruct #eqP %2 (@(ex_intro … N1)) % //
  |4,5,8,9:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1 %1 
   (@(ex_intro … M1)) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1 %2 
   (@(ex_intro … N1)) % //
  |#Q1 #M1 #red1 #_ #eqH destruct
  ]
qed.
  
lemma red_prod : ∀M,N,P. red (Prod M N) P →
 (∃M1. P = (Prod M1 N) ∧ red M M1) ∨
 (∃N1. P = (Prod M N1) ∧ red N N1).
#M #N #P #redMNP (inversion redMNP)
  [#P1 #M1 #N1 #eqH destruct
  |2,3: #M1 #N1 #eqH destruct 
  |4,5,6,7:#Q1 #Q2 #N1 #red1 #_ #eqH destruct
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %1
   (@(ex_intro … M1)) % //
  |#Q1 #M1 #N1 #red1 #_ #eqH destruct #eqP %2 
   (@(ex_intro … N1)) % //
  |#Q1 #M1 #red1 #_ #eqH destruct
  ]
qed.

definition reduct ≝ λn,m. red m n.

definition SN ≝ WF ? reduct.

definition NF ≝ λM. ∀N. ¬ (reduct N M).

theorem NF_to_SN: ∀M. NF M → SN M.
#M #nfM % #a #red @False_ind /2/
qed.

lemma NF_Sort: ∀i. NF (Sort i).
#i #N % #redN (inversion redN) 
  [1: #P #N #M #H destruct
  |2,3 :#N #M #H destruct
  |4,5,6,7,8,9: #N #M #P #_ #_ #H destruct
  |#M #N #_ #_ #H destruct
  ]
qed.

lemma NF_Rel: ∀i. NF (Rel i).
#i #N % #redN (inversion redN) 
  [1: #P #N #M #H destruct
  |2,3 :#N #M #H destruct
  |4,5,6,7,8,9: #N #M #P #_ #_ #H destruct
  |#M #N #_ #_ #H destruct
  ]
qed.

lemma SN_d : ∀M. SN M → SN (D M). 
#M #snM (elim snM) #b #H #Hind % #a #redd (cases (red_d … redd))
#Q * #eqa #redbQ >eqa @Hind //
qed. 

lemma SN_step: ∀N. SN N → ∀M. reduct M N → SN M.
#N * #b #H #M #red @H //.
qed. 

lemma sub_red: ∀M,N.subterm N M → ∀N1.red N N1 → 
∃M1.subterm N1 M1 ∧ red M M1.
#M #N #subN (elim subN) /4/
(* trsansitive case *)
#P #Q #S #subPQ #subQS #H1 #H2 #A #redP (cases (H1 ? redP))
#B * #subA #redQ (cases (H2 ? redQ)) #C * #subBC #redSC
@(ex_intro … C) /3/
qed.

axiom sub_star_red: ∀M,N.(star … subterm) N M → ∀N1.red N N1 → 
∃M1.subterm N1 M1 ∧ red M M1.
  
lemma SN_subterm: ∀M. SN M → ∀N.subterm N M → SN N.
#M #snM (elim snM) #M #snM #HindM #N #subNM % #N1 #redN 
(cases (sub_red … subNM ? redN)) #M1 *
#subN1M1 #redMM1 @(HindM … redMM1) //
qed.

lemma SN_subterm_star: ∀M. SN M → ∀N.(star … subterm N M) → SN N.
#M #snM #N #Hstar (cases (star_inv T subterm M N)) #_ #H
lapply (H Hstar) #Hstari (elim Hstari) //
#M #N #_ #subNM #snM @(SN_subterm …subNM) //
qed.

definition shrink ≝ λN,M. reduct N M ∨ (TC … subterm) N M.

definition SH ≝ WF ? shrink.

lemma SH_subterm: ∀M. SH M → ∀N.(star … subterm) N M → SH N.
#M #snM (elim snM) #M 
#snM #HindM #N #subNM (cases (star_case ???? subNM))
  [#eqNM >eqNM % /2/
  |#subsNM % #N1 *
    [#redN (cases (sub_star_red … subNM ? redN)) #M1 *
     #subN1M1 #redMM1 @(HindM M1) /2/
    |#subN1 @(HindM N) /2/ 
    ]
  ]
qed.

theorem SN_to_SH: ∀N. SN N → SH N.
#N #snN (elim snN) (@Telim_size) 
#b #Hsize #snb #Hind % #a * /2/ #subab @Hsize; 
  [(elim subab) 
    [#c #subac @size_subterm // 
    |#b #c #subab #subbc #sab @(transitive_lt … sab) @size_subterm //
    ]    
  |@SN_step @(SN_subterm_star b); 
    [% /2/ |@TC_to_star @subab] % @snb
  |#a1 #reda1 cases(sub_star_red b a ?? reda1);
    [#a2 * #suba1 #redba2 @(SH_subterm a2) /2/ |/2/ ]  
  ]
qed.

lemma SH_to_SN: ∀N. SH N → SN N.
@WF_antimonotonic /2/ qed.

lemma SN_Lambda: ∀N.SN N → ∀M.SN M → SN (Lambda N M).
#N #snN (elim snN) #P #shP #HindP #M #snM 
(* for M we proceed by induction on SH *)
(lapply (SN_to_SH ? snM)) #shM (elim shM)
#Q #shQ #HindQ % #a #redH (cases (red_lambda … redH))
  [* 
    [* #S * #eqa #redPS >eqa @(HindP S ? Q ?) // 
     @SH_to_SN % /2/ 
    |* #S * #eqa #redQS >eqa @(HindQ S) /2/
    ]
  |* #S * #eqQ #eqa >eqa @SN_d @(HindQ S) /3/
  ]
qed. 

(*
lemma SH_Lambda: ∀N.SH N → ∀M.SH M → SN (Lambda N M).
#N #snN (elim snN) #P #snP #HindP #M #snM (elim snM) 
#Q #snQ #HindQ % #a #redH (cases (red_lambda … redH))
  [* 
    [* #S * #eqa #redPS >eqa @(HindP S ? Q ?) /2/
     % /2/ 
    |* #S * #eqa #redQS >eqa @(HindQ S) /2/
    ]
  |* #S * #eqQ #eqa >eqa @SN_d @(HindQ S) /3/
  ]
qed. *)
 
lemma SN_Prod: ∀N.SN N → ∀M.SN M → SN (Prod N M).
#N #snN (elim snN) #P #shP #HindP #M #snM (elim snM)
#Q #snQ #HindQ % #a #redH (cases (red_prod … redH))
  [* #S * #eqa #redPS >eqa @(HindP S ? Q ?) // 
   % /2/ 
  |* #S * #eqa #redQS >eqa @(HindQ S) /2/
  ]
qed. 




