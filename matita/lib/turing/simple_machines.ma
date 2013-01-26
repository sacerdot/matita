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

include "turing/if_multi.ma".
include "turing/inject.ma".
include "turing/basic_machines.ma".

definition Rtc_multi_true ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
   (∃c. current alpha (nth i ? t1 (niltape ?)) = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_multi_false ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
    (∀c. current alpha (nth i ? t1 (niltape ?)) = Some ? c → test c = false) ∧ t2 = t1.

lemma sem_test_char_multi :
  ∀alpha,test,n,i.i ≤ n → 
  inject_TM ? (test_char ? test) n i ⊨ 
  [ tc_true : Rtc_multi_true alpha test n i, Rtc_multi_false alpha test n i ].
#alpha #test #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_char alpha test) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * * #c *
  #Hcur #Htestc #Hnth_i #Hnth_j %
  [ %{c} % //
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
| #Hqfalse lapply (Hfalse Hqfalse) * * #Htestc #Hnth_i #Hnth_j %
  [ @Htestc
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
qed.

definition Rm_test_null_true ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
   current alpha (nth i ? t1 (niltape ?)) ≠ None ? ∧ t2 = t1.
   
definition Rm_test_null_false ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
    current alpha (nth i ? t1 (niltape ?)) = None ? ∧ t2 = t1.

lemma sem_test_null_multi : ∀alpha,n,i.i ≤ n → 
  inject_TM ? (test_null ?) n i ⊨ 
    [ tc_true : Rm_test_null_true alpha n i, Rm_test_null_false alpha n i ].
#alpha #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_null alpha) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * #Hcur #Hnth_i #Hnth_j % //
  @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) #Hi0i
  [ >Hi0i @sym_eq @Hnth_i | @sym_eq @Hnth_j @sym_not_eq // ] ] 
| #Hqfalse lapply (Hfalse Hqfalse) * * #Hcur #Hnth_i #Hnth_j %
  [ @Hcur
  | @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) // 
    #Hi0i @sym_eq @Hnth_j @sym_not_eq // ] ] 
qed.
(* move a single tape *)
definition mmove_states ≝ initN 2.

definition mmove0 : mmove_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition mmove1 : mmove_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition trans_mmove ≝ 
 λi,sig,n,D.
 λp:mmove_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in match (pi1 … q) with
 [ O ⇒ 〈mmove1,change_vec ? (S n) (null_action ? n) (〈None ?,D〉) i〉
 | S _ ⇒ 〈mmove1,null_action sig n〉 ].

definition mmove ≝ 
  λi,sig,n,D.
  mk_mTM sig n mmove_states (trans_mmove i sig n D) 
    mmove0 (λq.q == mmove1).
    
definition Rm_multi ≝ 
  λalpha,n,i,D.λt1,t2:Vector ? (S n).
  t2 = change_vec ? (S n) t1 (tape_move alpha (nth i ? t1 (niltape ?)) D) i.
   
lemma sem_move_multi :
  ∀alpha,n,i,D.i ≤ n → 
  mmove i alpha n D ⊨ Rm_multi alpha n i D.
#alpha #n #i #D #Hin #int %{2}
%{(mk_mconfig ? mmove_states n mmove1 ?)} 
[| %
 [ whd in ⊢ (??%?); @eq_f whd in ⊢ (??%?); @eq_f %
 | whd >tape_move_multi_def
   <(change_vec_same … (ctapes …) i (niltape ?))
   >pmap_change <tape_move_multi_def >tape_move_null_action % ] ]
 qed.

(* simple copy with no move *)
definition copy_states ≝ initN 3.

definition cc0 : copy_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition cc1 : copy_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).

definition trans_copy_char_N ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ 〈cc1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,N〉) src)
           (〈nth src ? a (None ?),N〉) dst〉
 | S _ ⇒ 〈cc1,null_action ? n〉 ].

definition copy_char_N ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_states (trans_copy_char_N src dst sig n) 
    cc0 (λq.q == cc1).

definition R_copy_char_N ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  outt = change_vec ?? int
          (tape_write  ? (nth dst ? int (niltape ?))
            (current ? (nth src ? int (niltape ?)))) dst.

lemma copy_char_N_q0_q1 :
  ∀src,dst,sig,n,v.src ≠ dst → src < S n → dst < S n → 
  step sig n (copy_char_N src dst sig n) (mk_mconfig ??? cc0 v) =
    mk_mconfig ??? cc1 
     (change_vec ?? v
       (tape_write  ? (nth dst ? v (niltape ?))
          (current ? (nth src ? v (niltape ?)))) dst).
#src #dst #sig #n #v #Heq #Hsrc #Hdst
whd in ⊢ (??%?); @eq_f
<(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
<(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
>tape_move_multi_def
>pmap_change >pmap_change <tape_move_multi_def
>tape_move_null_action @eq_f3 //
[ >change_vec_same %
| >change_vec_same >change_vec_same >nth_current_chars // ]
qed.

lemma sem_copy_char_N:
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_char_N src dst sig n ⊨ R_copy_char_N src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
%{2} % [| % [ % | whd >copy_char_N_q0_q1 // ]]
qed.

(**************** copy and advance  ***********************)
definition copy_char_states ≝ initN 3.

definition trans_copy_char ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_char_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ 〈cc1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,R〉) src)
           (〈nth src ? a (None ?),R〉) dst〉
 | S _ ⇒ 〈cc1,null_action ? n〉 ].

definition copy_char ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_char_states (trans_copy_char src dst sig n) 
    cc0 (λq.q == cc1).

definition R_copy_char ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  outt = change_vec ?? 
         (change_vec ?? int
          (tape_move_mono ? (nth src ? int (niltape ?)) 〈None ?, R〉) src)
          (tape_move_mono ? (nth dst ? int (niltape ?)) 
           〈current ? (nth src ? int (niltape ?)), R〉) dst.

lemma copy_char_q0_q1 :
  ∀src,dst,sig,n,v.src ≠ dst → src < S n → dst < S n → 
  step sig n (copy_char src dst sig n) (mk_mconfig ??? cc0 v) =
    mk_mconfig ??? cc1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move_mono ? (nth src ? v (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? v (niltape ?)) 〈current ? (nth src ? v (niltape ?)), R〉) dst).
#src #dst #sig #n #v #Heq #Hsrc #Hdst
whd in ⊢ (??%?);
<(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
<(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
>tape_move_multi_def @eq_f2 //
>pmap_change >pmap_change <tape_move_multi_def
>tape_move_null_action @eq_f2 // @eq_f2
[ >change_vec_same %
| >change_vec_same >change_vec_same // ]
qed.

lemma sem_copy_char:
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_char src dst sig n ⊨ R_copy_char src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
%{2} % [| % [ % | whd >copy_char_q0_q1 // ]]
qed.



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

