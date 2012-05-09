(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)


(* COMPARE BIT

*)

include "turing/while_machine.ma".
include "turing/if_machine.ma".

(* ADVANCE TO MARK (right)

   sposta la testina a destra fino a raggiungere il primo carattere marcato 
   
*)

(* 0, a ≠ mark _ ⇒ 0, R
0, a = mark _ ⇒ 1, N *)

definition atm_states ≝ initN 3.

definition atmr_step ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha atm_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈1, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈1,None ?〉
     | false ⇒ 〈2,Some ? 〈a',R〉〉 ]])
  O (λx.notb (x == 0)).

definition Ratmr_step_true ≝ 
  λalpha,test,t1,t2.
   ∃ls,a,rs.
   t1 = midtape alpha ls a rs ∧ test a = false ∧ 
   t2 = mk_tape alpha (a::ls) (option_hd ? rs) (tail ? rs).
   
definition Ratmr_step_false ≝ 
  λalpha,test,t1,t2.
    t1 = t2 ∧
    (current alpha t1 = None ? ∨
     (∃a.current ? t1 = Some ? a ∧ test a = true)).
     
lemma atmr_q0_q1 :
  ∀alpha,test,ls,a0,rs. test a0 = true → 
  step alpha (atmr_step alpha test)
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) 1
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest normalize >Htest %
qed.
     
lemma atmr_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (atmr_step alpha test)
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) 2
    (mk_tape … (a0::ls) (option_hd ? rs) (tail ? rs)).
#alpha #test #ls #a0 #ts #Htest normalize >Htest cases ts //
qed.

lemma sem_atmr_step :
  ∀alpha,test.
  accRealize alpha (atmr_step alpha test) 
    2 (Ratmr_step_true alpha test) (Ratmr_step_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? 1 (niltape ?))) %
  [ % // #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (leftof ? a al)))
  % [ % // #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (rightof ? a al)))
  % [ % // #Hfalse destruct | #_ % // % % ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? 1 ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >atmr_q0_q1 //
        | #Hfalse destruct ]
      | #_ % // %2 @(ex_intro ?? c) % // ]
    ]
  | @(ex_intro ?? (mk_config ?? 2 (mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs))))
    % 
    [ %
      [ whd in ⊢ (??%?); >atmr_q0_q2 //
      | #_ @(ex_intro ?? ls) @(ex_intro ?? c) @(ex_intro ?? rs)
        % // % //
      ]
    | #Hfalse @False_ind @(absurd ?? Hfalse) %
    ]
  ]
]
qed.

definition R_adv_to_mark_r ≝ λalpha,test,t1,t2.
  ∀ls,c,rs.
  (t1 = midtape alpha ls c rs  → 
  ((test c = true ∧ t2 = t1) ∨
   (test c = false ∧
    ∀rs1,b,rs2. rs = rs1@b::rs2 → 
     test b = true → (∀x.memb ? x rs1 = true → test x = false) → 
     t2 = midtape ? (reverse ? rs1@c::ls) b rs2))).
     
definition adv_to_mark_r ≝ 
  λalpha,test.whileTM alpha (atmr_step alpha test) 2.

lemma wsem_adv_to_mark_r :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atmr_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 #ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
    #Hfalse destruct (Hfalse)
  | * #a * #Ha #Htest #ls #c #rs #H2 %
    >H2 in Ha; whd in ⊢ (??%? → ?); #Heq destruct (Heq) % //
    <Htapea //
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH
  #ls #c #rs #Htapea %2
  cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest #Htapeb
  
  >Htapea' in Htapea; #Htapea destruct (Htapea) % // *
  [ #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #_
    cases (IH … Htapeb)
    [ * #_ #Houtc >Houtc >Htapeb %
    | * #Hfalse >Hfalse in Htestb; #Htestb destruct (Htestb) ]
  | #r1 #rs1 #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #Hmemb
    cases (IH … Htapeb)
    [ * #Hfalse >(Hmemb …) in Hfalse;
      [ #Hft destruct (Hft)
      | @memb_hd ]
    | * #Htestr1 #H1 >reverse_cons >associative_append
      @H1 // #x #Hx @Hmemb @memb_cons //
    ]
  ]
qed.

lemma terminate_adv_to_mark_r :
  ∀alpha,test.
  ∀t.Terminate alpha (adv_to_mark_r alpha test) t.
#alpha #test #t
@(terminate_while … (sem_atmr_step alpha test))
  [ %
  | cases t
    [ % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    |2,3: #a0 #al0 % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    | #ls #c #rs generalize in match c; -c generalize in match ls; -ls
      elim rs
      [#ls #c % #t1 * #ls0 * #c0 * #rs0 * *
       #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1; 
       % #t2 * #ls1 * #c1 * #rs1 * * >Ht1
       normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
      | #r0 #rs0 #IH #ls #c % #t1 * #ls0 * #c0 * #rs0 * *
        #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1;
        >Ht1 @IH
      ]
    ]
  ]
qed.

lemma sem_adv_to_mark_r :
  ∀alpha,test.
  Realize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
/2/
qed.

(* MARK machine

   marks the current character 
 *)
 
definition mark_states ≝ initN 2.

definition mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) mark_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈1,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ let 〈a'',b〉 ≝ a' in 〈1,Some ? 〈〈a'',true〉,N〉〉
      | S q ⇒ 〈1,None ?〉 ] ])
  O (λq.q == 1).
  
definition R_mark ≝ λalpha,t1,t2.
  ∀ls,c,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls 〈c,b〉 rs → 
  t2 = midtape ? ls 〈c,true〉 rs.
    
lemma sem_mark :
  ∀alpha.Realize ? (mark alpha) (R_mark alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
| #ls * #c #b #rs
  @ex_intro [| % [ % | #ls0 #c0 #b0 #rs0 #H1 destruct (H1) % ] ] ]
qed.

(* MOVE RIGHT 

   moves the head one step to the right

*)

definition move_states ≝ initN 2.

definition move_r ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈1,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ 〈1,Some ? 〈a',R〉〉
      | S q ⇒ 〈1,None ?〉 ] ])
  O (λq.q == 1).
  
definition R_move_r ≝ λalpha,t1,t2.
  ∀ls,c,rs.
  t1 = midtape alpha ls c rs → 
  t2 = mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs).
    
lemma sem_move_r :
  ∀alpha.Realize ? (move_r alpha) (R_move_r alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
| #ls #c #rs
  @ex_intro [| % [ % | #ls0 #c0 #rs0 #H1 destruct (H1)
  cases rs0 // ] ] ]
qed.

(* MOVE LEFT

   moves the head one step to the right

*)

definition move_l ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈1,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ 〈1,Some ? 〈a',L〉〉
      | S q ⇒ 〈1,None ?〉 ] ])
  O (λq.q == 1).
  
definition R_move_l ≝ λalpha,t1,t2.
  ∀ls,c,rs.
  t1 = midtape alpha ls c rs → 
  t2 = mk_tape ? (tail ? ls) (option_hd ? ls) (c::rs).
    
lemma sem_move_l :
  ∀alpha.Realize ? (move_l alpha) (R_move_l alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #rs #Hfalse destruct ] ]
| #ls #c #rs
  @ex_intro [| % [ % | #ls0 #c0 #rs0 #H1 destruct (H1)
  cases ls0 // ] ] ]
qed.

(* MOVE RIGHT AND MARK machine

   marks the first character on the right
   
   (could be rewritten using (mark; move_right))
 *)
 
definition mrm_states ≝ initN 3.

definition move_right_and_mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) mrm_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈2,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ 〈1,Some ? 〈a',R〉〉
      | S q ⇒ match q with
        [ O ⇒ let 〈a'',b〉 ≝ a' in
              〈2,Some ? 〈〈a'',true〉,N〉〉
        | S _ ⇒ 〈2,None ?〉 ] ] ])
  O (λq.q == 2).
  
definition R_move_right_and_mark ≝ λalpha,t1,t2.
  ∀ls,c,d,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls c (〈d,b〉::rs) → 
  t2 = midtape ? (c::ls) 〈d,true〉 rs.
    
lemma sem_move_right_and_mark :
  ∀alpha.Realize ? (move_right_and_mark alpha) (R_move_right_and_mark alpha).
#alpha #intape @(ex_intro ?? 3) cases intape
[ @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
| #ls #c *
  [ @ex_intro [| % [ % | #ls0 #c0 #d0 #b0 #rs0 #Hfalse destruct ] ]
  | * #d #b #rs @ex_intro
    [| % [ % | #ls0 #c0 #d0 #b0 #rs0 #H1 destruct (H1) % ] ] ] ]
qed.

(* CLEAR MARK machine

   clears the mark in the current character 
 *)
 
definition clear_mark_states ≝ initN 3.

definition clear_mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) clear_mark_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈1,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ let 〈a'',b〉 ≝ a' in 〈1,Some ? 〈〈a'',false〉,N〉〉
      | S q ⇒ 〈1,None ?〉 ] ])
  O (λq.q == 1).
  
definition R_clear_mark ≝ λalpha,t1,t2.
  ∀ls,c,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls 〈c,b〉 rs → 
  t2 = midtape ? ls 〈c,false〉 rs.
    
lemma sem_clear_mark :
  ∀alpha.Realize ? (clear_mark alpha) (R_clear_mark alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #b #rs #Hfalse destruct ] ]
| #ls * #c #b #rs
  @ex_intro [| % [ % | #ls0 #c0 #b0 #rs0 #H1 destruct (H1) % ] ] ]
qed.

(* ADVANCE MARK RIGHT machine

   clears mark on current char,
   moves right, and marks new current char
   
*)

definition adv_mark_r ≝ 
  λalpha:FinSet.
    seq ? (clear_mark alpha)
      (seq ? (move_r ?) (mark alpha)).
      
definition R_adv_mark_r ≝ λalpha,t1,t2.
  ∀ls,c,d,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls 〈c,true〉 (〈d,b〉::rs) → 
  t2 = midtape ? (〈c,false〉::ls) 〈d,true〉 rs.
  
lemma sem_adv_mark_r : 
  ∀alpha.Realize ? (adv_mark_r alpha) (R_adv_mark_r alpha).
#alpha #intape
cases (sem_seq ????? (sem_clear_mark …) 
         (sem_seq ????? (sem_move_r ?) (sem_mark alpha)) intape)
#k * #outc * #Hloop whd in ⊢ (%→?);
* #ta * whd in ⊢ (%→?); #Hs1 * #tb * whd in ⊢ (%→%→?); #Hs2 #Hs3
@(ex_intro ?? k) @(ex_intro ?? outc) %
[ @Hloop
| -Hloop #ls #c #d #b #rs #Hintape @(Hs3 … b)
  @(Hs2 ls 〈c,false〉 (〈d,b〉::rs))
  @(Hs1 … Hintape)
]
qed.

(* ADVANCE TO MARK (left)

axiomatized

*)

definition R_adv_to_mark_l ≝ λalpha,test,t1,t2.
  ∀ls,c,rs.
  (t1 = midtape alpha ls c rs  → 
  ((test c = true ∧ t2 = t1) ∨
   (test c = false ∧
    ∀ls1,b,ls2. ls = ls1@b::ls2 → 
     test b = true → (∀x.memb ? x ls1 = true → test x = false) → 
     t2 = midtape ? ls2 b (reverse ? ls1@c::rs)))).

axiom adv_to_mark_l : ∀alpha:FinSet.(alpha → bool) → TM alpha.
(* definition adv_to_mark_l ≝ 
  λalpha,test.whileTM alpha (atml_step alpha test) 2. *)

axiom wsem_adv_to_mark_l :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_l alpha test) (R_adv_to_mark_l alpha test).
(*
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atmr_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 #ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
    #Hfalse destruct (Hfalse)
  | * #a * #Ha #Htest #ls #c #rs #H2 %
    >H2 in Ha; whd in ⊢ (??%? → ?); #Heq destruct (Heq) % //
    <Htapea //
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH
  #ls #c #rs #Htapea %2
  cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest #Htapeb
  
  >Htapea' in Htapea; #Htapea destruct (Htapea) % // *
  [ #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #_
    cases (IH … Htapeb)
    [ * #_ #Houtc >Houtc >Htapeb %
    | * #Hfalse >Hfalse in Htestb; #Htestb destruct (Htestb) ]
  | #r1 #rs1 #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #Hmemb
    cases (IH … Htapeb)
    [ * #Hfalse >(Hmemb …) in Hfalse;
      [ #Hft destruct (Hft)
      | @memb_hd ]
    | * #Htestr1 #H1 >reverse_cons >associative_append
      @H1 // #x #Hx @Hmemb @memb_cons //
    ]
  ]
qed.
*)

axiom terminate_adv_to_mark_l :
  ∀alpha,test.
  ∀t.Terminate alpha (adv_to_mark_l alpha test) t.
(*
#alpha #test #t
@(terminate_while … (sem_atmr_step alpha test))
  [ %
  | cases t
    [ % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    |2,3: #a0 #al0 % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    | #ls #c #rs generalize in match c; -c generalize in match ls; -ls
      elim rs
      [#ls #c % #t1 * #ls0 * #c0 * #rs0 * *
       #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1; 
       % #t2 * #ls1 * #c1 * #rs1 * * >Ht1
       normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
      | #r0 #rs0 #IH #ls #c % #t1 * #ls0 * #c0 * #rs0 * *
        #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1;
        >Ht1 @IH
      ]
    ]
  ]
qed.
*)

lemma sem_adv_to_mark_l :
  ∀alpha,test.
  Realize alpha (adv_to_mark_l alpha test) (R_adv_to_mark_l alpha test).
/2/
qed.

(*
   ADVANCE BOTH MARKS machine
   
   l1 does not contain marks ⇒
   

   input:
   l0 x* a l1 x0* a0 l2
              ^
   
   output:
   l0 x a* l1 x0 a0* l2
        ^
*)

definition is_marked ≝ 
  λalpha.λp:FinProd … alpha FinBool.
  let 〈x,b〉 ≝ p in b.

definition adv_both_marks ≝ 
  λalpha.seq ? (adv_mark_r alpha)
    (seq ? (move_l ?)
     (seq ? (adv_to_mark_l (FinProd alpha FinBool) (is_marked alpha))
       (adv_mark_r alpha))).

definition R_adv_both_marks ≝ 
  λalpha,t1,t2.
    ∀l0,x,a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2) → 
    t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (reverse ? l1@〈x0,false〉::〈a0,true〉::l2).

lemma sem_adv_both_marks :
  ∀alpha.Realize ? (adv_both_marks alpha) (R_adv_both_marks alpha).    
#alpha #intape
cases (sem_seq ????? (sem_adv_mark_r …) 
        (sem_seq ????? (sem_move_l …)
          (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?)) 
            (sem_adv_mark_r alpha))) intape)
#k * #outc * #Hloop whd in ⊢ (%→?);
* #ta * whd in ⊢ (%→?); #Hs1 * #tb * whd in ⊢ (%→?); #Hs2
* #tc * whd in ⊢ (%→%→?); #Hs3 #Hs4
@(ex_intro ?? k) @(ex_intro ?? outc) %
[ @Hloop
| -Hloop #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape
  @(Hs4 … false) -Hs4
  lapply (Hs1 … Hintape) #Hta
  lapply (Hs2 … Hta) #Htb
  cases (Hs3 … Htb)
  [ * #Hfalse normalize in Hfalse; destruct (Hfalse)
  | * #_ -Hs3 #Hs3 
    lapply (Hs3 (l1@[〈a,false〉]) 〈x,true〉 l0 ???)
    [ #x1 #Hx1 cases (memb_append … Hx1)
      [ @Hl1
      | #Hx1' >(memb_single … Hx1') % ]
    | % 
    | >associative_append %
    | >reverse_append #Htc @Htc ]
  ]
qed.
  
inductive unialpha : Type[0] ≝ 
| bit : bool → unialpha
| comma : unialpha
| bar : unialpha
| grid : unialpha.

definition unialpha_eq ≝ 
  λa1,a2.match a1 with
  [ bit x ⇒ match a2 with [ bit y ⇒ ¬ xorb x y | _ ⇒ false ]
  | comma ⇒ match a2 with [ comma ⇒ true | _ ⇒ false ]
  | bar ⇒ match a2 with [ bar ⇒ true | _ ⇒ false ]
  | grid ⇒ match a2 with [ grid ⇒ true | _ ⇒ false ] ].
  
definition DeqUnialpha ≝ mk_DeqSet unialpha unialpha_eq ?.
* [ #x * [ #y cases x cases y normalize % // #Hfalse destruct
         | *: normalize % #Hfalse destruct ]
  |*: * [1,5,9,13: #y ] normalize % #H1 destruct % ]
qed.

definition FSUnialpha ≝ 
  mk_FinSet DeqUnialpha [bit true;bit false;comma;bar;grid] ?.
@daemon
qed.

(* 
   MATCH AND ADVANCE(f)
   
   input:
   l0 x* a l1 x0* a0 l2
              ^
    
   output:
   l0 x a* l1 x0 a0* l2   (f(x0) == true)
        ^
   l0 x* a l1 x0* a0 l2   (f(x0) == false)
              ^
*)

include "turing/universal/tests.ma".

(* NO OPERATION

  t1 = t2
  *)
  
definition nop_states ≝ initN 1.

definition nop ≝ 
  λalpha:FinSet.mk_TM alpha nop_states
  (λp.let 〈q,a〉 ≝ p in 〈q,None ?〉)
  O (λ_.true).
  
definition R_nop ≝ λalpha.λt1,t2:tape alpha.t2 = t1.

lemma sem_nop :
  ∀alpha.Realize alpha (nop alpha) (R_nop alpha).
#alpha #intape @(ex_intro ?? 1) @ex_intro [| % normalize % ]
qed.

definition match_and_adv ≝ 
  λalpha,f.ifTM ? (test_char ? f)
     (adv_both_marks alpha) (nop ?) tc_true.

definition R_match_and_adv ≝ 
  λalpha,f,t1,t2.
    ∀l0,x,a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2) → 
    (f 〈x0,true〉 = true ∧ t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (reverse ? l1@〈x0,false〉::〈a0,true〉::l2))
    ∨ (f 〈x0,true〉 = false ∧ t2 = t1).

lemma sem_match_and_adv : 
  ∀alpha,f.Realize ? (match_and_adv alpha f) (R_match_and_adv alpha f).
#alpha #f #intape
cases (sem_if ? (test_char ? f) … tc_true (sem_test_char ? f) (sem_adv_both_marks alpha) (sem_nop ?) intape)
#k * #outc * #Hloop #Hif @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop
cases Hif
[ * #ta * whd in ⊢ (%→%→?); #Hta #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape
  >Hintape in Hta; #Hta cases (Hta … (refl ??)) -Hta #Hf #Hta % % 
  [ @Hf | @Houtc [ @Hl1 | @Hta ] ]
| * #ta * whd in ⊢ (%→%→?); #Hta #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape
  >Hintape in Hta; #Hta cases (Hta … (refl ??)) -Hta #Hf #Hta %2 %
  [ @Hf | >Houtc @Hta ]
]
qed.

(*
 if x = c
      then move_right; ----
           adv_to_mark_r;
           if current (* x0 *) = 0
              then advance_mark ----
                   adv_to_mark_l;
                   advance_mark
              else STOP
      else M
*)

definition comp_step_subcase ≝ 
  λalpha,c,elseM.ifTM ? (test_char ? (λx.x == c))
    (seq ? (move_r …)
      (seq ? (adv_to_mark_r ? (is_marked alpha)) 
      (match_and_adv ? (λx.x == c))))
    elseM tc_true.

definition R_comp_step_subcase ≝ 
  λalpha,c,RelseM,t1,t2.
    ∀l0,x,a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    t1 = midtape (FinProd … alpha FinBool)
           l0 〈x,true〉 (〈a,false〉::l1@〈x0,true〉::〈a0,false〉::l2) → 
    (〈x,true〉 = c ∧ x = x0 ∧
     t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (l1@〈x0,false〉::〈a0,true〉::l2))
    ∨ (〈x,true〉 = c ∧ x ≠ x0 ∧
     t2 = midtape (FinProd … alpha FinBool) 
        (reverse ? l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2))     
    ∨ (〈x,true〉 ≠ c ∧ RelseM t1 t2).

lemma sem_comp_step_subcase : 
  ∀alpha,c,elseM,RelseM.
  Realize ? elseM RelseM → 
  Realize ? (comp_step_subcase alpha c elseM) 
    (R_comp_step_subcase alpha c RelseM).
#alpha #c #elseM #RelseM #Helse #intape
cases (sem_if ? (test_char ? (λx.x == c)) … tc_true 
        (sem_test_char ? (λx.x == c)) 
        (sem_seq ????? (sem_move_r …)
          (sem_seq ????? (sem_adv_to_mark_r ? (is_marked alpha))
             (sem_match_and_adv ? (λx.x == c)))) Helse intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop cases HR -HR
[ * #ta * whd in ⊢ (%→?); #Hta * #tb * whd in ⊢ (%→?); #Htb
  * #tc * whd in ⊢ (%→?); #Htc whd in ⊢ (%→?); #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape %
  >Hintape in Hta; #Hta cases (Hta ? (refl ??)) -Hta
  #Hx #Hta lapply (Htb … Hta) -Htb #Htb
  cases (Htc … Htb) [ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
  -Htc * #_ #Htc lapply (Htc l1 〈x0,true〉 (〈a0,false〉::l2) (refl ??) (refl ??) Hl1)
  -Htc #Htc cases (Houtc ???????? Htc) -Houtc
  [ * #Hx0 #Houtc % %
    [ % [ @(\P Hx) | <(\P Hx0) in Hx; #Hx lapply (\P Hx) #Hx' destruct (Hx') % ]
    | >Houtc >reverse_reverse % ]
  | * #Hx0 #Houtc %2 %
    [ % [ @(\P Hx) | <(\P Hx) in Hx0; #Hx0 lapply (\Pf Hx0) @not_to_not #Hx' >Hx' %]
    | >Houtc @Htc ]
  | (* members of lists are invariant under reverse *) @daemon ]
| * #ta * whd in ⊢ (%→?); #Hta #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape %2
  >Hintape in Hta; #Hta cases (Hta ? (refl ??)) -Hta #Hx #Hta %
  [ @(\Pf Hx)
  | <Hta @Houtc ]
]
qed.



(*
   MARK NEXT TUPLE machine
   (partially axiomatized)
   
   marks the first character after the first bar (rightwards)
 *)

axiom myalpha : FinSet.
axiom is_bar : FinProd … myalpha FinBool → bool.
axiom is_grid : FinProd … myalpha FinBool → bool.
definition bar_or_grid ≝ λc.is_bar c ∨ is_grid c.
axiom bar : FinProd … myalpha FinBool.
axiom grid : FinProd … myalpha FinBool.

definition mark_next_tuple ≝ 
  seq ? (adv_to_mark_r ? bar_or_grid)
     (ifTM ? (test_char ? is_bar)
       (move_r_and_mark ?) (nop ?) 1).

definition R_mark_next_tuple ≝ 
  λt1,t2.
    ∀ls,c,rs1,rs2.
    (* c non può essere un separatore ... speriamo *)
    t1 = midtape ? ls c (rs1@grid::rs2) → 
    memb ? grid rs1 = false → bar_or_grid c = false → 
    (∃rs3,rs4,d,b.rs1 = rs3 @ bar :: rs4 ∧
      memb ? bar rs3 = false ∧ 
      Some ? 〈d,b〉 = option_hd ? (rs4@grid::rs2) ∧
      t2 = midtape ? (bar::reverse ? rs3@c::ls) 〈d,true〉 (tail ? (rs4@grid::rs2)))
    ∨
    (memb ? bar rs1 = false ∧ 
     t2 = midtape ? (reverse ? rs1@c::ls) grid rs2).
     
axiom tech_split :
  ∀A:DeqSet.∀f,l.
   (∀x.memb A x l = true → f x = false) ∨
   (∃l1,c,l2.f c = true ∧ l = l1@c::l2 ∧ ∀x.memb ? x l1 = true → f c = false).
(*#A #f #l elim l
[ % #x normalize #Hfalse *)
     
theorem sem_mark_next_tuple :
  Realize ? mark_next_tuple R_mark_next_tuple.
#intape 
lapply (sem_seq ? (adv_to_mark_r ? bar_or_grid)
         (ifTM ? (test_char ? is_bar) (mark ?) (nop ?) 1) ????)
[@sem_if //
| //
|||#Hif cases (Hif intape) -Hif
   #j * #outc * #Hloop * #ta * #Hleft #Hright
   @(ex_intro ?? j) @ex_intro [|% [@Hloop] ]
   -Hloop
   #ls #c #rs1 #rs2 #Hrs #Hrs1 #Hc
   cases (Hleft … Hrs)
   [ * #Hfalse >Hfalse in Hc; #Htf destruct (Htf)
   | * #_ #Hta cases (tech_split ? is_bar rs1)
     [ #H1 lapply (Hta rs1 grid rs2 (refl ??) ? ?)
       [ (* Hrs1, H1 *) @daemon
       | (* bar_or_grid grid = true *) @daemon
       | -Hta #Hta cases Hright
         [ * #tb * whd in ⊢ (%→?); #Hcurrent
           @False_ind cases(Hcurrent grid ?)
           [ #Hfalse (* grid is not a bar *) @daemon
           | >Hta % ]
         | * #tb * whd in ⊢ (%→?); #Hcurrent
           cases (Hcurrent grid ?)
           [  #_ #Htb whd in ⊢ (%→?); #Houtc
             %2 %
             [ (* H1 *) @daemon
             | >Houtc >Htb >Hta % ]
           | >Hta % ]
         ]
       ]
    | * #rs3 * #c0 * #rs4 * * #Hc0 #Hsplit #Hrs3
      % @(ex_intro ?? rs3) @(ex_intro ?? rs4)
     lapply (Hta rs3 c0 (rs4@grid::rs2) ???)
     [ #x #Hrs3' (* Hrs1, Hrs3, Hsplit *) @daemon
     | (* bar → bar_or_grid *) @daemon
     | >Hsplit >associative_append % ] -Hta #Hta
       cases Hright
       [ * #tb * whd in ⊢ (%→?); #Hta'
         whd in ⊢ (%→?); #Htb
         cases (Hta' c0 ?)
         [ #_ #Htb' >Htb' in Htb; #Htb
           generalize in match Hsplit; -Hsplit
           cases rs4 in Hta;
           [ >(eq_pair_fst_snd … grid)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst grid)) @(ex_intro ?? (\snd grid))
               % [ % [ % [ (* Hsplit *) @daemon |(*Hrs3*) @daemon ] | % ] | % ] 
                     | (* Hc0 *) @daemon ]
           | #r5 #rs5 >(eq_pair_fst_snd … r5)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst r5)) @(ex_intro ?? (\snd r5))
               % [ % [ % [ (* Hc0, Hsplit *) @daemon | (*Hrs3*) @daemon ] | % ]
                     | % ] | (* Hc0 *) @daemon ] ] | >Hta % ]
             | * #tb * whd in ⊢ (%→?); #Hta'
               whd in ⊢ (%→?); #Htb
               cases (Hta' c0 ?)
               [ #Hfalse @False_ind >Hfalse in Hc0;
                 #Hc0 destruct (Hc0)
               | >Hta % ]
]]]]
qed.