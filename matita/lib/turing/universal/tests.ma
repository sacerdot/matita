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

definition tc_true ≝ 1.

definition test_char ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha tc_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈1, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈1,None ?〉
     | false ⇒ 〈2,None ?〉 ]])
  O (λx.notb (x == 0)).

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
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) 1
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest normalize >Htest %
qed.
     
lemma tc_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (test_char alpha test)
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (test_char alpha test)) 2
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest normalize >Htest %
qed.

lemma sem_test_char :
  ∀alpha,test.
  accRealize alpha (test_char alpha test) 
    1 (Rtc_true alpha test) (Rtc_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? 1 (niltape ?))) %
  [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (leftof ? a al)))
  % [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (rightof ? a al)))
  % [ % // #_ #c normalize #Hfalse destruct | #_ #c normalize #Hfalse destruct (Hfalse) ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? 1 ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >tc_q0_q1 //
        | #_ #c0 #Hc0 % // normalize in Hc0; destruct // ]
      | * #Hfalse @False_ind @Hfalse % ]
    ]
  | @(ex_intro ?? (mk_config ?? 2 (midtape ? ls c rs)))
    % 
    [ %
      [ whd in ⊢ (??%?); >tc_q0_q2 //
      | #Hfalse destruct (Hfalse) ]
    | #_ #c0 #Hc0 % // normalize in Hc0; destruct (Hc0) //
    ]
  ]
]
qed.