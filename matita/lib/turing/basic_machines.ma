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

include "turing/while_machine.ma".

(******************* write a given symbol under the head **********************)
definition write_states ≝ initN 2.

definition wr0 : write_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition wr1 : write_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition write ≝ λalpha,c.
  mk_TM alpha write_states
  (λp.let 〈q,a〉 ≝ p in
    match pi1 … q with 
    [ O ⇒ 〈wr1,Some ? 〈c,N〉〉
    | S _ ⇒ 〈wr1,None ?〉 ])
  wr0 (λx.x == wr1).
  
definition R_write ≝ λalpha,c,t1,t2.
  ∀ls,x,rs.t1 = midtape alpha ls x rs → t2 = midtape alpha ls c rs.
  
lemma sem_write : ∀alpha,c.Realize ? (write alpha c) (R_write alpha c).
#alpha #c #t @(ex_intro … 2) @ex_intro
  [|% [% |#ls #c #rs #Ht >Ht % ] ]
qed. 
 
(******************** moves the head one step to the right ********************)

definition move_states ≝ initN 2.
definition move0 : move_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition move1 : move_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition move_r ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈move1,None ?〉
    | Some a' ⇒ match (pi1 … q) with
      [ O ⇒ 〈move1,Some ? 〈a',R〉〉
      | S q ⇒ 〈move1,None ?〉 ] ])
  move0 (λq.q == move1).
  
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

(******************** moves the head one step to the left *********************)

definition move_l ≝ 
  λalpha:FinSet.mk_TM alpha move_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈move1,None ?〉
    | Some a' ⇒ match pi1 … q with
      [ O ⇒ 〈move1,Some ? 〈a',L〉〉
      | S q ⇒ 〈move1,None ?〉 ] ])
  move0 (λq.q == move1).
  
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

(********************************* test char **********************************)

(* the test_char machine ends up in two different states q1 and q2 wether or not
the current character satisfies a boolean test function passed as a parameter to
the machine.
The machine ends up in q1 also in case there is no current character.
*)

definition tc_states ≝ initN 3.

definition tc_start : tc_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition tc_true : tc_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition tc_false : tc_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition test_char ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha tc_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈tc_true, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈tc_true,None ?〉
     | false ⇒ 〈tc_false,None ?〉 ]])
  tc_start (λx.notb (x == tc_start)).

definition Rtc_true ≝ 
  λalpha,test,t1,t2.
   ∀c. current alpha t1 = Some ? c → test c = true ∧ t2 = t1.
   
definition Rtc_false ≝ 
  λalpha,test,t1,t2.
    ∀c. current alpha t1 = Some ? c → test c = false ∧ t2 = t1.
     
lemma tc_q0_q1 :
  ∀alpha,test,ls,a0,rs. test a0 = true → 
  step alpha (test_char alpha test)
    (mk_config ?? tc_start (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) tc_true
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?); 
whd in match (trans … 〈?,?〉); >Htest %
qed.
     
lemma tc_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (test_char alpha test)
    (mk_config ?? tc_start (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) tc_false
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?); 
whd in match (trans … 〈?,?〉); >Htest %
qed.

lemma sem_test_char :
  ∀alpha,test.
  accRealize alpha (test_char alpha test) 
    tc_true (Rtc_true alpha test) (Rtc_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? tc_true (niltape ?))) %
  [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? tc_true (leftof ? a al)))
  % [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? tc_true (rightof ? a al)))
  % [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? tc_true ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >tc_q0_q1 //
        | #_ #c0 #Hc0 % // normalize in Hc0; destruct // ]
      | * #Hfalse @False_ind @Hfalse % ]
    ]
  | @(ex_intro ?? (mk_config ?? tc_false (midtape ? ls c rs)))
    % 
    [ %
      [ whd in ⊢ (??%?); >tc_q0_q2 //
      | whd in ⊢ ((??%%)→?); #Hfalse destruct (Hfalse) ]
    | #_ #c0 #Hc0 % // normalize in Hc0; destruct (Hc0) //
    ]
  ]
]
qed.

