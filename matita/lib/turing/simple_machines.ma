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

include "turing/multi_universal/match.ma".

(********************** look_ahead test *************************)

definition mtestR ≝ λsig,i,n,test.
  (mmove i sig n R) · 
    (ifTM ?? (inject_TM ? (test_char ? test) n i)
    (single_finalTM ?? (mmove i sig n L))
    (mmove i sig n L) tc_true).


(* underspecified *)
definition RmtestR_true ≝ λsig,i,n,test.λt1,t2:Vector ? n.
  ∀ls,c,c1,rs.
    nth i ? t1 (niltape ?) = midtape sig ls c (c1::rs) →
    t1 = t2 ∧ (test c1 = true).

definition RmtestR_false ≝ λsig,i,n,test.λt1,t2:Vector ? n.
  ∀ls,c,c1,rs.
    nth i ? t1 (niltape ?) = midtape sig ls c (c1::rs) →
    t1 = t2 ∧ (test c1 = false).   
    
definition mtestR_acc: ∀sig,i,n,test.states ?? (mtestR sig i n test). 
#sig #i #n #test @inr @inr @inl @inr @start_nop 
qed.

lemma sem_mtestR: ∀sig,i,n,test. i ≤ n →
  mtestR sig i n test ⊨ 
    [mtestR_acc sig i n test: 
       RmtestR_true sig  i (S n) test, RmtestR_false sig i (S n) test].
#sig #i #n #test #Hlein
@(acc_sem_seq_app sig n … (sem_move_multi … R Hlein)
   (acc_sem_if sig n ????????
     (sem_test_char_multi sig test n i Hlein)
     (sem_move_multi … L Hlein)
     (sem_move_multi … L Hlein)))
  [#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); * *
   #cx #Hcx #Htx #Ht2 #ls #c #c1 #rs #Ht1
   >Ht1 in Hmove; whd in match (tape_move ???); #Ht3 
   >Ht3 in Hcx; >nth_change_vec [|@le_S_S //] * whd in ⊢ (??%?→?);
   #Hsome destruct (Hsome) #Htest % [2:@Htest]
   >Htx in Ht2; whd in ⊢ (%→?); #Ht2 @(eq_vec … (niltape ?))
   #j #lejn cases (true_or_false (eqb i j)) #Hij
    [lapply lejn <(eqb_true_to_eq … Hij) #lein >Ht2 >nth_change_vec [2://]
     >Ht3 >nth_change_vec >Ht1 // 
    |lapply (eqb_false_to_not_eq … Hij) #Hneq >Ht2 >nth_change_vec_neq [2://]
     >Ht3 >nth_change_vec_neq //
    ]
  |#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); *
   #Hcx #Heqtx #Htx #ls #c #c1 #rs #Ht1
   >Ht1 in Hmove; whd in match (tape_move ???); #Ht3 
   >Ht3 in Hcx; >nth_change_vec [2:@le_S_S //] #Hcx lapply (Hcx ? (refl ??)) 
   #Htest % // @(eq_vec … (niltape ?))
   #j #lejn cases (true_or_false (eqb i j)) #Hij
    [lapply lejn <(eqb_true_to_eq … Hij) #lein >Htx >nth_change_vec [2://]
     >Heqtx >Ht3 >nth_change_vec >Ht1 // 
    |lapply (eqb_false_to_not_eq … Hij) #Hneq >Htx >nth_change_vec_neq [2://]
     >Heqtx >Ht3 >nth_change_vec_neq //
    ]
  ]
qed.

