(* include "turing/auxiliary_machines.ma". *)

include "turing/multi_to_mono/shift_trace.ma".
include "turing/multi_universal/normalTM.ma". (* for DeqMove *)

(******************************************************************************)

(* exec_move_R : before shifting the trace left - to simulate a right move of
the head - we must be sure we are not in rightoverflow, that is that the symbol 
at the right of the head, if any, is not blank *)

(* a simple look-ahead machine *)
definition mtestR ≝ λsig,test.
  (move sig R) · 
    (ifTM ? (test_char ? test)
    (single_finalTM ? (move sig L))
    (move sig L) tc_true).

(* underspecified *)
definition RmtestR_true ≝ λsig,test.λt1,t2.
  ∀ls,c,rs.
    t1 = midtape sig ls c rs → 
    ∃c1,rs1. rs = c1::rs1 ∧ t1 = t2 ∧ (test c1 = true).

definition RmtestR_false ≝ λsig,test.λt1,t2.
  (∀ls,c,c1,rs.
    t1 = midtape sig ls c (c1::rs) →
    t1 = t2 ∧ (test c1 = false)) ∧
  (∀ls,c.
    t1 = midtape sig ls c [] → t1 = t2).
    
definition mtestR_acc: ∀sig,test.states ? (mtestR sig test). 
#sig #test @inr @inr @inl @inr @start_nop 
qed.

lemma sem_mtestR: ∀sig,test.
  mtestR sig test ⊨ 
    [mtestR_acc sig test: 
       RmtestR_true sig  test, RmtestR_false sig test].
#sig #test 
@(acc_sem_seq_app sig … (sem_move_single  … )
   (acc_sem_if sig …
     (sem_test_char sig test)
     (sem_move_single  … )
     (sem_move_single … )))
  [#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); * *
   #cx * #Hcx #H1cx #Htx #Ht2 #ls #c #rs #Ht1
   >Ht1 in Hmove; cases rs 
    [#H >H in Hcx; whd in ⊢ (??%?→?); #H1 destruct (H1)
    |#c1 #rs1 #Ht3 %{c1} %{rs1} %
      [% [//|>Htx in Ht2; >Ht3 whd in ⊢ (%→?); #H @sym_eq @H ]
      |>Ht3 in Hcx; whd in ⊢ (??%?→?); #H1 destruct (H1) //
      ]
    ]
  |#t1 #t2 #t3 whd in ⊢ (%→?); #Hmove * #tx * whd in  ⊢ (%→?); *
   #Hcx #Heqtx #Htx %
    [#ls #c #c1 #rs #Ht1
     >Ht1 in Hmove; whd in match (tape_move ???); #Ht3 
     >Ht3 in Hcx; #Hcx lapply (Hcx ? (refl ??)) 
     #Htest % // >Heqtx in Htx; >Ht3 whd in ⊢ (%→?); #H @sym_eq @H
    |#ls0 #c0 #Ht1 >Ht1 in Hmove; whd in match (tape_move ???);
     <Heqtx #H1tx >H1tx in Htx; #H @sym_eq @H
    ]
  ]
qed.

definition guarded_M ≝ λsig,n,i,M.
  (ifTM ? (test_char ? (no_blank sig n i))
   M
   (ifTM ? (mtestR ? (no_blank sig n i))
    M
    (nop ?) (mtestR_acc …)) tc_true).
    
definition R_guarded_M ≝ λsig,n,i,RM,t1,t2. 
  ∀ls,a,rs. t1 = midtape ? ls a rs → 
   (no_blank sig n i a = false → 
     no_blank sig n i (hd ? rs (all_blank …)) = false → t1=t2) ∧
   (no_blank sig n i a = true ∨
     no_blank sig n i (hd ? rs (all_blank …)) = true → RM t1 t2).

lemma sem_R_guarded: ∀sig,n,i,M,RM. M ⊨ RM →
   guarded_M sig n i M ⊨ R_guarded_M sig n i RM.
#sig #n #i #M #RM #HM 
@(sem_if_app … (sem_test_char … ) HM
  (sem_if … (sem_mtestR … ) HM (sem_nop ?)))
#tin #tout #t1 *
  [* * * #c * #Hc #H1c #Ht1 #Htout #ls #a #rs #Htin 
   >Htin in Hc; normalize in ⊢ (%→?); #H1 destruct (H1) %
    [>H1c #H2 @False_ind destruct (H2)
    |#H1 <Htin <Ht1 @Htout
    ]
  |* * #Hc #Ht1 #H #ls #a #rs lapply (Hc a) <Ht1 -Ht1 #Ha #Ht1  
   cases H
    [* #t2 * #Ht2 lapply (Ht2 … Ht1)
     * #c1 * #rs1 * * #H1 #H2 #H3 #H4 % [2: //]
     #Ha >H1 whd in match (hd ???); >H3 #H destruct (H)
    |lapply Ht1 -Ht1 cases rs
      [#Ht1 * #t2 * * #_ #Ht2 lapply (Ht2 … Ht1) -Ht2 #Ht2
       whd in ⊢ (%→?); #Htout % [//] * 
        [>Ha [#H destruct (H)| >Ht1 %] 
        |whd in ⊢ (??%?→?); >blank_all_blank whd in ⊢ (??%?→?);
         #H destruct (H)
        ]
      |#c #rs1 #Ht1 * #t2 * * #Ht2 #_ lapply (Ht2 … Ht1) -Ht2 * 
       #Ht2 whd in ⊢ (??%?→?); #Hnb whd in ⊢ (%→?); #Htout % [//] * 
        [>Ha [#H destruct (H)| >Ht1 %] 
        |whd in ⊢ (??%?→?); whd in match (hd ???); >Hnb whd in ⊢ (??%?→?);
         #H destruct (H)
        ]
      ]
    ]
  ]
qed.

definition move_R_i ≝ λsig,n,i. guarded_M sig n i (mtiL sig n i).

definition Rmove_R_i ≝ λsig,n,i. R_guarded_M sig n i (Rmtil sig n i).


(*************************** readback of the tape *****************************)

definition opt_cur ≝ λsig,a. 
  if a == blank sig then None ? else Some ? a.

definition rb_trace ≝ λsig,ls,a,rs.
  mk_tape ? (to_blank ? ls) (opt_cur sig a) (to_blank ? rs).

lemma rb_trace_def: ∀sig,ls,a,rs.
  rb_trace sig ls a rs = 
    mk_tape ? (to_blank ? ls) (opt_cur sig a) (to_blank ? rs).
// qed.
  
definition rb_trace_i ≝ λsig,n,ls,a,rs,i.
  rb_trace sig (trace ? n i ls) (nth i ? a (blank ?)) (trace ? n i rs).

lemma rb_trace_i_def: ∀sig,n,ls,a,rs,i.
  rb_trace_i sig n ls a rs i = 
    rb_trace sig (trace ? n i ls) (nth i ? a (blank ?)) (trace ? n i rs).
// qed.

let rec readback sig n ls a rs i on i : Vector (tape (sig_ext sig)) i ≝
  match i with 
  [ O ⇒ mk_Vector ? 0 (nil ?) (refl ??)
  | S j ⇒ vec_cons ? (rb_trace_i sig n ls a rs j) j (readback sig n ls a rs j)
  ].

lemma orb_false_l: ∀b1,b2:bool. 
  (b1 ∨ b2) = false → (b1 = false) ∧ (b2 = false).
* * normalize /2/ qed.

lemma no_blank_true_to_not_blank: ∀sig,n,a,i. 
  (no_blank sig n i a = true) → nth i ? (vec … n a) (blank sig) ≠ blank ?.
#sig #n #a #i #H @(not_to_not … (eqnot_to_noteq … false H))
-H #H normalize >H % 
qed.

lemma rb_move_R : ∀sig,n,ls,a,rs,outt,i.
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  Rmove_R_i … i (midtape ? ls a rs) outt → 
  ∃ls1,a1,rs1. 
   outt = midtape ? ls1 a1 rs1 ∧
   (∀i.regular_trace sig n a1 ls1 rs1 i) ∧ 
   rb_trace_i sig n ls1 (vec … a1) rs1 i = 
     tape_move ? (rb_trace_i sig n ls (vec … a) rs i) R ∧
   ∀j. j ≤n → j ≠ i → 
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j.
#sig #n #ls #a #rs #outt #i #Hreg #Hha #Hhls #Hhrs #Hmove
lapply (Hmove … (refl …)) -Hmove * #HMove1 #HMove2
cases (true_or_false (no_blank sig n i a ∨ 
        no_blank sig n i (hd (multi_sig sig n) rs (all_blank sig n))))
  [2: #Hcase cases (orb_false_l … Hcase) -Hcase #Hb1 #Hb2 
   lapply (HMove1 … Hb1 Hb2) #Hout %{ls} %{a} %{rs}
   %[%[%[@sym_eq @Hout |@Hreg]
      |>rb_trace_i_def
       cut (nth i ? (vec … a) (blank ?) = blank sig)
        [@(\P ?) @injective_notb @Hb1] #Ha >Ha
       >rb_trace_def whd in match (opt_cur ??);
       cut (to_blank sig (trace sig n i rs) = [])
        [@daemon] #Hrs >Hrs 
       cases (to_blank sig (trace sig n i ls)) // 
      ]
    |//]
  |-HMove1 #Hb 
   lapply(HMove2 (orb_true_l … Hb) … (refl …) Hha Hreg ? Hhls Hhrs) -HMove2 
    [#Hb1 lapply Hb -Hb  whd in match (no_blank sig n i a);
     >Hb1 #H @no_blank_true_to_not_blank @H] 
   * #ls1 * #a1 * #rs1 * * * * * #H1 #H2 #H3 #H4 #H5 #H6
   %{ls1} %{a1} %{rs1} 
   %[%[%[@H1|@H2]
      |(* either a is blank or not *)
       cases (true_or_false (no_blank sig n i a)) #Hba
        [(* a not blank *) 
         >rb_trace_i_def >rb_trace_def <to_blank_i_def >H5 >to_blank_cons_nb
          [2: @no_blank_true_to_not_blank //]        
         lapply H6 -H6 #Hrs >(rb_trace_i_def … rs i) >rb_trace_def 
         <(to_blank_i_def … rs) <Hrs
         cut (opt_cur sig (nth i ? (vec … a) (blank sig)) =
              Some ? (nth i ? (vec … a) (blank sig))) [@daemon] #Ha >Ha
         (* either a1 is blank or not *)
         cases (true_or_false (no_blank sig n i a1)) #Hba1
          [cut (opt_cur sig (nth i ? (vec … a1) (blank sig)) =
                Some ? (nth i ? (vec … a1) (blank sig))) [@daemon] #Ha1 >Ha1
           >to_blank_cons_nb [%|@(\Pf ?) @injective_notb @Hba1]
          |cut (opt_cur sig (nth i ? (vec … a1) (blank sig)) = None ?) [@daemon] 
           #Ha1 >Ha1 
           cut (to_blank_i … i (a1::rs1) = [ ]) [@daemon] #Ha1rs1 >Ha1rs1
           cut (to_blank_i … i rs1 = [ ]) [@daemon] #Hrs1 <to_blank_i_def >Hrs1 %
          ]
        |>rb_trace_i_def >rb_trace_def <to_blank_i_def (* >H5 >to_blank_cons_nb *) 
         >rb_trace_i_def >rb_trace_def <(to_blank_i_def … rs) <H6 >H5
         cut (to_blank_i … i (a::ls) = [ ]) [@daemon] #Hals >Hals
         cut (to_blank_i … i ls = [ ]) [@daemon] #Hls <(to_blank_i_def … ls) >Hls
         cut (opt_cur sig (nth i ? (vec … a) (blank sig)) = None ?) [@daemon] #Ha >Ha
         cut (nth i ? (vec … a1) (blank ?) ≠ blank ?) [@daemon] #Ha1 
         >(to_blank_cons_nb … Ha1)
         cut (opt_cur sig (nth i ? (vec … a1) (blank sig)) =
              Some ? (nth i ? (vec … a1) (blank sig))) [@daemon] -Ha1 #Ha1 >Ha1 %
        ]
      ]
    |(* case j ≠ i *)
     #j #Hle #Hneq >rb_trace_i_def >rb_trace_i_def >rb_trace_def >rb_trace_def 
     <(to_blank_i_def … rs) <(to_blank_i_def … rs1) >(H4 j Hle Hneq)
     cut ((to_blank_i sig n j ls1 = to_blank_i sig n j ls) ∧ 
          (opt_cur sig (nth j (sig_ext sig) (vec … a1) (blank sig)) =  
           opt_cur sig (nth j (sig_ext sig) (vec … a) (blank sig))))
      [@daemon] * #H7 #H8 >H7 >H8 //
    ]
  ]
qed.

definition Rmove_R_i_rb ≝ λsig,n,i,t1,t2.
∀ls,a,rs.
  t1 = midtape ? ls a rs →
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (multi_sig sig n) ls1 a1 rs1 ∧
   (∀i.regular_trace sig n a1 ls1 rs1 i) ∧
   rb_trace_i sig n ls1 (vec … a1) rs1 i = 
     tape_move ? (rb_trace_i sig n ls (vec … a) rs i) R ∧
   ∀j. j ≤n → j ≠ i → 
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j.

lemma sem_move_R_i : ∀sig,n,i.i < n →
  move_R_i sig n i ⊨ Rmove_R_i_rb sig n i.
#sig #n #i #ltin @(Realize_to_Realize … (Rmove_R_i sig n i))
  [#t1 #t2 #H #ls #a #rs #H1 #H2 #H3 #H4 #H5 @rb_move_R // <H1 // 
  |@sem_R_guarded @sem_Rmtil //
  ]
qed.
  
(* move_L_i axiomatized *)

axiom move_L_i : ∀sig.∀n,i:nat.TM (multi_sig sig n).

definition Rmove_L_i_rb ≝ λsig,n,i,t1,t2.
∀ls,a,rs.
  t1 = midtape ? ls a rs →
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (multi_sig sig n) ls1 a1 rs1 ∧
   (∀i.regular_trace sig n a1 ls1 rs1 i) ∧
   rb_trace_i sig n ls1 (vec … a1) rs1 i = 
     tape_move ? (rb_trace_i sig n ls (vec … a) rs i) L ∧
   ∀j. j ≤n → j ≠ i → 
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j.
      
axiom sem_move_L_i : ∀sig,n,i.i < n →
  move_L_i sig n i ⊨ Rmove_L_i_rb sig n i.
  
(*
lemma rb_move_L : ∀sig,n,ls,a,rs,outt,i.
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  Rmove_L_i … i (midtape ? ls a rs) outt → 
  ∃ls1,a1,rs1. 
   outt = midtape ? ls1 a1 rs1 ∧
   rb_trace_i sig n ls1 (vec … a1) rs1 i = 
     tape_move ? (rb_trace_i sig n ls (vec … a) rs i) L ∧
   ∀j. j ≤n → j ≠ i → 
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j. *)

(* The following function read a move from  a vector of moves and executes it *)

axiom get_move : ∀sig.∀n.∀a:multi_sig sig n.nat → DeqMove. 

definition exec_move_i ≝ λsig,n,i.
    (ifTM ? (test_char ? (λa. (get_move sig n a i == R)))
      (move_R_i sig n i)
      (ifTM ? (test_char ? (λa. (get_move sig n a i == L)))
        (move_L_i sig n i)
        (nop ?) tc_true) tc_true).
        
definition R_exec_move_i ≝ λsig,n,i,t1,t2.
∀a,ls,rs. 
  t1 = midtape ? ls a rs → 
  (∀i.regular_trace sig n a ls rs i) → 
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  ∃ls1,a1,rs1. 
   t2 = midtape (multi_sig sig n) ls1 a1 rs1 ∧
   (∀i.regular_trace sig n a1 ls1 rs1 i) ∧
   rb_trace_i sig n ls1 (vec … a1) rs1 i = 
     tape_move ? (rb_trace_i sig n ls (vec … a) rs i) (get_move sig n a i) ∧
   ∀j. j ≤n → j ≠ i → 
    rb_trace_i sig n ls1 (vec … a1) rs1 j = 
      rb_trace_i sig n ls (vec … a) rs j.

lemma  tape_move_N: ∀A,t. tape_move A t N = t.
// qed.

lemma sem_exec_move_i: ∀sig,n,i. i < n →
  exec_move_i sig n i ⊨ R_exec_move_i sig n i.
#sig #n #i #ltin
@(sem_if_app … (sem_test_char …)
  (sem_move_R_i … ltin) 
  (sem_if … (sem_test_char …)
    (sem_move_L_i … ltin) (sem_nop ?)))
#tin #tout #t1 *
  [* * * #c * #Hc #HR #Ht1 #HMR 
   #a #ls #rs #Htin >Htin in Hc; whd in ⊢ (??%?→?); #H destruct (H)
    >(\P HR) @HMR >Ht1 @Htin
  |* * #HR #Ht1 >Ht1 *
    [* #t2 * * * #c * #Hc #HL #Ht2 #HML 
     #a #ls #rs #Htin >Htin in Hc; whd in ⊢ (??%?→?); #H destruct (H)
     >(\P HL) @HML >Ht2 @Htin
    |* #t2 * * #HL #Ht2 >Ht2 whd in ⊢ (%→?); #Htout >Htout
     #a #ls #rs #Htin >Htin in HR; #HR >Htin in HL; #HL  
     cut (get_move sig n a i = N)
      [lapply (HR a (refl … )) lapply (HL a (refl … ))
       cases (get_move sig n a i) normalize 
        [#H destruct (H) |#_ #H destruct (H) | //]]
     #HN >HN >tape_move_N #Hreg #_ #_ #_
     %{ls} %{a} %{rs} 
     %[%[%[%|@Hreg] |%] | //]
    ]
  ]
qed.

axiom reg_inv : ∀sig,n,a,ls,rs,a1,ls1,rs1. 
  regular_trace sig n a1 ls1 rs1 n →  
  (rb_trace_i sig n ls1 (vec … a1) rs1 n = 
      rb_trace_i sig n ls (vec  … n a) rs n) →
  nth n ? (vec … a) (blank ?) = head ? → 
  no_head_in … ls →
  no_head_in … rs →
  nth n ? (vec … a1) (blank ?) = head ? ∧ 
  no_head_in … ls1 ∧ no_head_in … rs1.













