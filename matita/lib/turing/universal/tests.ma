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

include "turing/if_machine.ma".

(* TEST CHAR 

   stato finale diverso a seconda che il carattere 
   corrente soddisfi un test booleano oppure no  
   
   q1 = true or no current char
   q2 = false
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
   ∀c. current alpha t1 = Some ? c → 
   test c = true ∧ t2 = t1.
   
definition Rtc_false ≝ 
  λalpha,test,t1,t2.
    ∀c. current alpha t1 = Some ? c → 
    test c = false ∧ t2 = t1.
     
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