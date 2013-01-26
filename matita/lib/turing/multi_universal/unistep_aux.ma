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

include "turing/multi_universal/moves_2.ma".
include "turing/multi_universal/match.ma".
include "turing/multi_universal/copy.ma".
include "turing/multi_universal/alphabet.ma".
include "turing/multi_universal/tuples.ma".

(*

  in.obj : ...  x ...
                ^
  in.cfg : ...  ? ? ...
                    ^
                
  out.cfg : ... 1 x ...
                  ^
                  
  ---------------------
  current (in.obj) = None
  
  in.cfg : ...  ? ? ...
                    ^

  out.cfg : ... 0 0 ...
                  ^
                  
  obj_to_cfg ≝ 
    move_l(cfg);
    move_l(cfg);
    (if (current(in.obj)) == None
       then write(0,cfg);
            move_r(cfg);
            write(0,cfg);
       else write(1,cfg);
            move_r(cfg);
            copy_step(obj,cfg);
            move_l(obj);)
    move_to_end_l(cfg);
    move_r(cfg);
       
  
  cfg_to_obj
*)

definition obj ≝ (0:DeqNat).
definition cfg ≝ (1:DeqNat).
definition prg ≝ (2:DeqNat).

definition obj_to_cfg ≝
  (ifTM ?? (inject_TM ? (test_null ?) 2 obj)
    (copy_char_N obj cfg FSUnialpha 2)
    (inject_TM ? (write FSUnialpha null) 2 cfg)
     tc_true) ·
  inject_TM ? (move_to_end FSUnialpha L) 2 cfg ·
  mmove cfg FSUnialpha 2 R.
  
definition R_obj_to_cfg ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = midtape ? ls c [ ] → 
  (∀lso,x,rso.nth obj ? t1 (niltape ?) = midtape FSUnialpha lso x rso → 
   t2 = change_vec ?? t1 
         (mk_tape ? [ ] (option_hd ? (reverse ? (x::ls))) (tail ? (reverse ? (x::ls)))) cfg) ∧
  (current ? (nth obj ? t1 (niltape ?)) = None ? → 
   t2 = change_vec ?? t1
         (mk_tape ? [ ] (option_hd FSUnialpha (reverse ? (null::ls))) 
           (tail ? (reverse ? (null::ls)))) cfg).

axiom accRealize_to_Realize :
  ∀sig,n.∀M:mTM sig n.∀Rtrue,Rfalse,acc.
  M ⊨ [ acc: Rtrue, Rfalse ] →  M ⊨ Rtrue ∪ Rfalse.
  
lemma eq_mk_tape_rightof :
 ∀alpha,a,al.mk_tape alpha (a::al) (None ?) [ ] = rightof ? a al.
#alpha #a #al %
qed.

lemma tape_move_mk_tape_R :
  ∀sig,ls,c,rs.
  (c = None ? → ls = [ ] ∨ rs = [ ]) → 
  tape_move ? (mk_tape sig ls c rs) R =
  mk_tape ? (option_cons ? c ls) (option_hd ? rs) (tail ? rs).
#sig * [ * [ * | #c * ] | #l0 #ls0 * [ *
[| #r0 #rs0 #H @False_ind cases (H (refl ??)) #H1 destruct (H1) ] | #c * ] ] 
normalize //
qed.

lemma eq_vec_change_vec : ∀sig,n.∀v1,v2:Vector sig n.∀i,t,d.
  nth i ? v2 d = t → 
  (∀j.i ≠ j → nth j ? v1 d = nth j ? v2 d) → 
  v2 = change_vec ?? v1 t i.
#sig #n #v1 #v2 #i #t #d #H1 #H2 @(eq_vec … d)
#i0 #Hlt cases (decidable_eq_nat i0 i) #Hii0
[ >Hii0 >nth_change_vec //
| >nth_change_vec_neq [|@sym_not_eq //] @sym_eq @H2 @sym_not_eq // ]
qed.

lemma not_None_to_Some: ∀A.∀a. a ≠ None A → ∃b. a = Some ? b.
#A * /2/ * #H @False_ind @H %
qed. 

lemma sem_obj_to_cfg : obj_to_cfg ⊨  R_obj_to_cfg.
@(sem_seq_app FSUnialpha 2 ????? 
  (sem_if ??????????
   (sem_test_null_multi ?? obj ?)
   (sem_copy_char_N …)
   (sem_inject ???? cfg ? (sem_write FSUnialpha null)))
  (sem_seq ?????? (sem_inject ???? cfg ? (sem_move_to_end_l ?))
    (sem_move_multi ? 2 cfg R ?))) //
#ta #tout *
#tb * #Hif * #tc * #HM2 #HM3 #c #ls #Hcfg
(* Hif *)
cases Hif -Hif
[ * #t1 * * #Hcurta #Ht1 destruct (Ht1)
  lapply (not_None_to_Some … Hcurta) * #curta #Hcurtaeq
  whd in ⊢ (%→?); #Htb % [2: #Hcur @False_ind /2/]
  #lso #xo #rso #Hobjta cases HM2 whd in ⊢ (%→?); * #_
  #HM2 #Heq >Htb in HM2; >nth_change_vec [2: @leb_true_to_le %]
  >Hcfg >Hcurtaeq #HM2 lapply (HM2 … (refl ??)) -HM2 
  whd in match (left ??); whd in match (right ??);
  >reverse_cons #Htc >HM3 @(eq_vec … (niltape ?)) #i #lei2 
  cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
  [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
    [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
     <(Heq 0) [2:@eqb_false_to_not_eq %] >Htb
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [%|2:@eqb_false_to_not_eq %] 
    |#Hi >Hi >nth_change_vec // >nth_change_vec // >Htc
     >Hobjta in Hcurtaeq; whd in ⊢ (??%?→?); #Htmp destruct(Htmp)
     >tape_move_mk_tape_R [2: #_ %1 %] %
    ]
  |#Hi >Hi >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
   >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
   <(Heq 2) [2:@eqb_false_to_not_eq %] >Htb
   >nth_change_vec_neq [%|2:@eqb_false_to_not_eq %] 
  ]
| * #t1 * * #Hcurta #Ht1 destruct (Ht1)
  * whd in ⊢ (%→?); #Htb lapply (Htb … Hcfg) -Htb #Htb
  #Htbeq % 
    [#lso #xo #rso #Hmid @False_ind >Hmid in Hcurta;
     whd in ⊢ (??%?→?); #Htmp destruct (Htmp)]
  #_ cases HM2 whd in ⊢ (%→?); * #_
  #HM2 #Heq >Htb in HM2; #HM2 lapply (HM2 … (refl ??)) -HM2 
  #Htc >HM3 @(eq_vec … (niltape ?)) #i #lei2 
  cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
  [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
    [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     <(Heq 0) [2:@eqb_false_to_not_eq %] >Htb
     <(Htbeq 0) [2:@eqb_false_to_not_eq %] % 
    |#Hi >Hi >nth_change_vec // >nth_change_vec // >Htc
     >tape_move_mk_tape_R [2: #_ %1 %] >reverse_cons % 
    ]
  |#Hi >Hi >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
   >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
   <(Heq 2) [2:@eqb_false_to_not_eq %] 
   <(Htbeq 2) [%|@eqb_false_to_not_eq %] 
  ]
]
qed.

definition test_null_char ≝ test_char FSUnialpha (λc.c == null).

definition R_test_null_char_true ≝ λt1,t2.
  current FSUnialpha t1 = Some ? null ∧ t1 = t2.
  
definition R_test_null_char_false ≝ λt1,t2.
  current FSUnialpha t1 ≠ Some ? null ∧ t1 = t2.
  
lemma sem_test_null_char :
  test_null_char ⊨ [ tc_true : R_test_null_char_true, R_test_null_char_false].
#t1 cases (sem_test_char FSUnialpha (λc.c == null) t1) #k * #outc * * #Hloop #Htrue
#Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Houtc cases (Htrue ?) [| @Houtc] * #c * #Hcurt1 #Hcnull lapply (\P Hcnull)
  -Hcnull #H destruct (H) #Houtc1 %
  [ @Hcurt1 | <Houtc1 % ] ]
| #Houtc cases (Hfalse ?) [| @Houtc] #Hc #Houtc %
  [ % #Hcurt1 >Hcurt1 in Hc; #Hc lapply (Hc ? (refl ??)) 
    >(?:((null:FSUnialpha) == null) = true) [|@(\b (refl ??)) ]
    #H destruct (H)
  | <Houtc % ] ]
qed.

definition cfg_to_obj ≝
  mmove cfg FSUnialpha 2 L ·
  (ifTM ?? (inject_TM ? test_null_char 2 cfg)
    (nop ? 2)
    (copy_char_N cfg obj FSUnialpha 2)
    tc_true).
(* ·
  inject_TM ? (move_to_end FSUnialpha L) 2 cfg ·
  mmove cfg FSUnialpha 2 R. *)
  
definition R_cfg_to_obj ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls) (None ?) [ ] → 
  (c = null → t2 = change_vec ?? t1 (midtape ? ls c [ ]) cfg) ∧
  (c ≠ null → 
   t2 = change_vec ??
          (change_vec ?? t1
             (midtape ? (left ? (nth obj ? t1 (niltape ?))) c (right ? (nth obj ? t1 (niltape ?)))) obj)
          (midtape ? ls c [ ]) cfg).
          
lemma tape_move_mk_tape_L :
  ∀sig,ls,c,rs.
  (c = None ? → ls = [ ] ∨ rs = [ ]) → 
  tape_move ? (mk_tape sig ls c rs) L =
  mk_tape ? (tail ? ls) (option_hd ? ls) (option_cons ? c rs).
#sig * [ * [ * | #c * ] | #l0 #ls0 * [ *
[| #r0 #rs0 #H @False_ind cases (H (refl ??)) #H1 destruct (H1) ] | #c * ] ] 
normalize //
qed.

lemma sem_cfg_to_obj : cfg_to_obj ⊨  R_cfg_to_obj.
@(sem_seq_app FSUnialpha 2 ????? (sem_move_multi ? 2 cfg L ?)
  (sem_if ??????????
   (acc_sem_inject ?????? cfg ? sem_test_null_char)
   (sem_nop …)
   (sem_copy_char_N …)))
// [@sym_not_eq //]
#ta #tb *
#tc * whd in ⊢ (%→?); #Htc *
[ * #te * * * #Hcurtc #Hte1 #Hte2 whd in ⊢ (%→?); #Htb destruct (Htb)
  #c #ls #Hta %
  [ #Hc >Hta in Htc; >eq_mk_tape_rightof whd in match (tape_move ???); #Htc
    cut (te = tc)
    [ lapply (eq_vec_change_vec ??????? (sym_eq … Hte1) Hte2) >change_vec_same // ]
      -Hte1 -Hte2 #Hte //
    | #Hc >Hta in Htc; >eq_mk_tape_rightof whd in match (tape_move ???); #Htc
      >Htc in Hcurtc; >nth_change_vec // normalize in ⊢ (%→?); 
      #H destruct (H) @False_ind cases Hc /2/ ]
| * #te * * * #Hcurtc #Hte1 #Hte2
  whd in ⊢ (%→?); #Htb
  #c #ls #Hta % #Hc
  [ >Htc in Hcurtc; >Hta >nth_change_vec // 
    normalize in ⊢ (%→?); * #H @False_ind /2/
  | cut (te = tc)
    [ lapply (eq_vec_change_vec ??????? (sym_eq … Hte1) Hte2)
      >change_vec_same // ] -Hte1 -Hte2 #Hte destruct (Hte)
    >Hta in Htc; whd in match (tape_move ???); #Htc
    >Htc in Htb; >nth_change_vec // 
    >nth_change_vec_neq [2:@eqb_false_to_not_eq //] >Hta 
    #Htb @Htb
  ]
qed.

definition char_to_move ≝ λc.match c with
  [ bit b ⇒ if b then R else L
  | _ ⇒ N].

definition char_to_bit_option ≝ λc.match c with
  [ bit b ⇒ Some ? (bit b)
  | _ ⇒ None ?]. 

definition R_cfg_to_obj1 ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls) (None ?) [ ] → 
  c ≠ bar →
  let new_obj ≝ 
      tape_write ? (nth obj ? t1 (niltape ?)) (char_to_bit_option c) in
    t2 = change_vec ??
          (change_vec ?? t1
            (tape_write ? (nth obj ? t1 (niltape ?)) (char_to_bit_option c)) obj)
          (midtape ? ls c [ ]) cfg.

lemma sem_cfg_to_obj1: cfg_to_obj ⊨  R_cfg_to_obj1.
@(Realize_to_Realize … sem_cfg_to_obj) #t1 #t2 #H #c #ls #Hcfg #Hbar
cases (H c ls Hcfg) cases (true_or_false (c==null)) #Hc
  [#Ht2 #_ >(Ht2 (\P Hc)) -Ht2 @(eq_vec … (niltape ?))
   #i #lei2 cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
    [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
      [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
       >nth_change_vec_neq in ⊢ (???%); [2:@eqb_false_to_not_eq %]
       >nth_change_vec // >(\P Hc) % 
      |#Hi >Hi >nth_change_vec //
      ] 
    |#Hi >Hi >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %] %
    ]
  |#_ #Ht2 >(Ht2 (\Pf Hc)) -Ht2 @(eq_vec … (niltape ?))
   #i #lei2 cases (le_to_or_lt_eq … (le_S_S_to_le …lei2))
    [#lei1 cases (le_to_or_lt_eq … (le_S_S_to_le …lei1))
      [#lei0 lapply(le_n_O_to_eq … (le_S_S_to_le …lei0)) #eqi <eqi
       >nth_change_vec_neq [2:@eqb_false_to_not_eq %] 
       >nth_change_vec_neq in ⊢ (???%); [2:@eqb_false_to_not_eq %]
       >nth_change_vec // >nth_change_vec // 
       lapply (\bf Hbar) lapply Hc elim c //
        [whd in ⊢ (??%?→?); #H destruct (H)
        |#_ whd in ⊢ (??%?→?); #H destruct (H)
        ]
      |#Hi >Hi >nth_change_vec //
      ] 
    |#Hi >Hi >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %]
     >nth_change_vec_neq [2:@eqb_false_to_not_eq %] %
    ]
  ]
qed.
       

(* macchina che muove il nastro obj a destra o sinistra a seconda del valore
   del current di prg, che codifica la direzione in cui ci muoviamo *)
      
definition tape_move_obj : mTM FSUnialpha 2 ≝ 
  ifTM ?? 
   (inject_TM ? (test_char ? (λc:FSUnialpha.c == bit false)) 2 prg)
   (mmove obj FSUnialpha 2 L)
   (ifTM ?? 
    (inject_TM ? (test_char ? (λc:FSUnialpha.c == bit true)) 2 prg)
    (mmove obj FSUnialpha 2 R)
    (nop ??)
    tc_true)
   tc_true.

definition R_tape_move_obj' ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  (current ? (nth prg ? t1 (niltape ?)) = Some ? (bit false) → 
   t2 = change_vec ?? t1 (tape_move ? (nth obj ? t1 (niltape ?)) L) obj) ∧
  (current ? (nth prg ? t1 (niltape ?)) = Some ? (bit true) → 
   t2 = change_vec ?? t1 (tape_move ? (nth obj ? t1 (niltape ?)) R) obj) ∧
  (current ? (nth prg ? t1 (niltape ?)) ≠ Some ? (bit false) →
   current ? (nth prg ? t1 (niltape ?)) ≠ Some ? (bit true) →  
   t2 = t1).
   
lemma sem_tape_move_obj' : tape_move_obj ⊨ R_tape_move_obj'.
#ta cases (sem_if ??????????
  (acc_sem_inject ?????? prg ? (sem_test_char ? (λc:FSUnialpha.c == bit false)))
  (sem_move_multi ? 2 obj L ?)
  (sem_if ??????????
   (acc_sem_inject ?????? prg ? (sem_test_char ? (λc:FSUnialpha.c == bit true)))
   (sem_move_multi ? 2 obj R ?)
   (sem_nop …)) ta) //
#i * #outc * #Hloop #HR %{i} %{outc} % [@Hloop] -i
cases HR -HR
[ * #tb * * * * #c * #Hcurta_prg #Hc lapply (\P Hc) -Hc #Hc #Htb1 #Htb2
  whd in ⊢ (%→%); #Houtc >Houtc -Houtc % [ %
  [ >Hcurta_prg #H destruct (H) >(?:tb = ta) 
    [| lapply (eq_vec_change_vec ??????? Htb1 Htb2)
       >change_vec_same // ] %
  | >Hcurta_prg #H destruct (H) destruct (Hc) ]
  | >Hcurta_prg >Hc * #H @False_ind /2/ ]
| * #tb * * * #Hnotfalse #Htb1 #Htb2 cut (tb = ta) 
  [ lapply (eq_vec_change_vec ??????? Htb1 Htb2)
     >change_vec_same // ] -Htb1 -Htb2 #Htb destruct (Htb) *
  [ * #tc * * * * #c * #Hcurta_prg #Hc lapply (\P Hc) -Hc #Hc #Htc1 #Htc2
    whd in ⊢ (%→%); #Houtc >Houtc -Houtc % [ %
    [ >Hcurta_prg #H destruct (H) destruct (Hc)
    | >Hcurta_prg #H destruct (H) >(?:tc = ta) 
      [| lapply (eq_vec_change_vec ??????? Htc1 Htc2)
        >change_vec_same // ] % ]
    | >Hcurta_prg >Hc #_ * #H @False_ind /2/ ]
  | * #tc * * * #Hnottrue #Htc1 #Htc2 cut (tc = ta) 
    [ lapply (eq_vec_change_vec ??????? Htc1 Htc2)
      >change_vec_same // ] -Htc1 -Htc2 
    #Htc destruct (Htc) whd in ⊢ (%→?); #Houtc % [ %
    [ #Hcurta_prg lapply (\Pf (Hnotfalse ? Hcurta_prg)) * #H @False_ind /2/
    | #Hcurta_prg lapply (\Pf (Hnottrue ? Hcurta_prg)) * #H @False_ind /2/ ]
    | #_ #_ @Houtc ]
  ]
]
qed.

definition R_tape_move_obj ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c. current ? (nth prg ? t1 (niltape ?)) = Some ? c → 
  t2 = change_vec ?? t1 (tape_move ? (nth obj ? t1 (niltape ?)) (char_to_move c)) obj.

lemma sem_tape_move_obj : tape_move_obj ⊨ R_tape_move_obj.
@(Realize_to_Realize … sem_tape_move_obj')
#ta #tb * * #Htb1 #Htb2 #Htb3 * [ *
[ @Htb2 | @Htb1 ] 
| #Hcurta_prg change with (nth obj ? ta (niltape ?)) in match (tape_move ???);
  >change_vec_same @Htb3 >Hcurta_prg % #H destruct (H)
| #Hcurta_prg change with (nth obj ? ta (niltape ?)) in match (tape_move ???);
  >change_vec_same @Htb3 >Hcurta_prg % #H destruct (H)
]
qed.

definition list_of_tape ≝ λsig.λt:tape sig.
  reverse ? (left ? t)@option_cons ? (current ? t) (right ? t).

definition restart_tape ≝ λi,n. 
  mmove i FSUnialpha n L ·
  inject_TM ? (move_to_end FSUnialpha L) n i ·
  mmove i FSUnialpha n R.
  
definition R_restart_tape ≝ λi,n.λint,outt:Vector (tape FSUnialpha) (S n).
   ∀t.t = nth i ? int (niltape ?) → 
   outt = change_vec ?? int 
    (mk_tape ? [ ] (option_hd ? (list_of_tape ? t)) (tail ? (list_of_tape ? t))) i.

lemma sem_restart_tape : ∀i,n.i < S n → restart_tape i n ⊨ R_restart_tape i n.
#i #n #Hleq
@(sem_seq_app ??????? (sem_move_multi ? n i L ?)
  (sem_seq ?????? (sem_inject ???? i ? (sem_move_to_end_l ?))
   (sem_move_multi ? n i R ?))) [1,2,3:@le_S_S_to_le //]
#ta #tb * #tc * whd in ⊢ (%→?); #Htc
* #td * * * #Htd1 #Htd2 #Htd3 
whd in ⊢ (%→?); #Htb *
[ #Hta_i <Hta_i in Htc; whd in ⊢ (???(????%?)→?); #Htc
  cut (td = tc) [@daemon] 
  (* >Htc in Htd1; >nth_change_vec // *) -Htd1 -Htd2 -Htd3
  #Htd >Htd in Htb; >Htc >change_vec_change_vec >nth_change_vec //
  #Htb >Htb %
| #r0 #rs0 #Hta_i <Hta_i in Htc; whd in ⊢ (???(????%?)→?); #Htc
  cut (td = tc) [@daemon] 
  (* >Htc in Htd1; >nth_change_vec // *) -Htd1 -Htd2 -Htd3
  #Htd >Htd in Htb; >Htc >change_vec_change_vec >nth_change_vec //
  #Htb >Htb %
| #l0 #ls0 #Hta_i <Hta_i in Htc; whd in ⊢ (???(????%?)→?); #Htc
  cut (td = change_vec ?? tc (mk_tape ? [ ] (None ?) (reverse ? ls0@[l0])) i)
  [@daemon]
  #Htd >Htd in Htb; >Htc >change_vec_change_vec >change_vec_change_vec
  >nth_change_vec // #Htb >Htb <(reverse_reverse ? ls0) in ⊢ (???%);
  cases (reverse ? ls0)
  [ %
  | #l1 #ls1 >reverse_cons
     >(?: list_of_tape ? (rightof ? l0 (reverse ? ls1@[l1])) =
          l1::ls1@[l0])
     [|change with (reverse ??@?) in ⊢ (??%?);
       whd in match (left ??); >reverse_cons >reverse_append 
       whd in ⊢ (??%?); @eq_f >reverse_reverse normalize >append_nil % ] % ]
| * 
  [ #c #rs #Hta_i <Hta_i in Htc; whd in ⊢ (???(????%?)→?); #Htc
    cut (td = tc) [@daemon] 
    (* >Htc in Htd1; >nth_change_vec // *) -Htd1 -Htd2 -Htd3
    #Htd >Htd in Htb; >Htc >change_vec_change_vec >nth_change_vec //
    #Htb >Htb %
  | #l0 #ls0 #c #rs #Hta_i <Hta_i in Htc; whd in ⊢ (???(????%?)→?); #Htc
    cut (td = change_vec ?? tc (mk_tape ? [ ] (None ?) (reverse ? ls0@l0::c::rs)) i)
    [@daemon]
    #Htd >Htd in Htb; >Htc >change_vec_change_vec >change_vec_change_vec
    >nth_change_vec // #Htb >Htb <(reverse_reverse ? ls0) in ⊢ (???%);
    cases (reverse ? ls0)
    [ %
    | #l1 #ls1 >reverse_cons
      >(?: list_of_tape ? (midtape ? (l0::reverse ? ls1@[l1]) c rs) =
            l1::ls1@l0::c::rs)
      [|change with (reverse ??@?) in ⊢ (??%?);
        whd in match (left ??); >reverse_cons >reverse_append 
        whd in ⊢ (??%?); @eq_f >reverse_reverse normalize
        >associative_append % ] % ]
  ]
]
qed.

