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
  mmove cfg FSUnialpha 2 L ·
  (ifTM ?? (inject_TM ? (test_null ?) 2 obj)
    (copy_step obj cfg FSUnialpha 2 ·
     mmove cfg FSUnialpha 2 L ·
     mmove obj FSUnialpha 2 L) 
    (inject_TM ? (write FSUnialpha null) 2 cfg)
     tc_true) ·
  inject_TM ? (move_to_end FSUnialpha L) 2 cfg ·
  mmove cfg FSUnialpha 2 R.
  
definition R_obj_to_cfg ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls) (None ?) [ ] → 
  (∀lso,x,rso.nth obj ? t1 (niltape ?) = midtape FSUnialpha lso x rso → 
   t2 = change_vec ?? t1 
         (mk_tape ? [ ] (option_hd ? (reverse ? (x::ls))) (tail ? (reverse ? (x::ls)))) cfg) ∧
  (current ? (nth obj ? t1 (niltape ?)) = None ? → 
   t2 = change_vec ?? t1
         (mk_tape ? [ ] (option_hd FSUnialpha (reverse ? (null::ls))) 
           (tail ? (reverse ? (null::ls)))) cfg).
           
axiom sem_move_to_end_l : ∀sig. move_to_end sig L ⊨ R_move_to_end_l sig.
axiom accRealize_to_Realize :
  ∀sig,n.∀M:mTM sig n.∀Rtrue,Rfalse,acc.
  M ⊨ [ acc: Rtrue, Rfalse ] →  M ⊨ Rtrue ∪ Rfalse.
  
lemma eq_mk_tape_rightof :
 ∀alpha,a,al.mk_tape alpha (a::al) (None ?) [ ] = rightof ? a al.
#alpha #a #al %
qed.

axiom daemon : ∀P:Prop.P.

definition option_cons ≝ λsig.λc:option sig.λl.
  match c with [ None ⇒ l | Some c0 ⇒ c0::l ].

lemma tape_move_mk_tape_R :
  ∀sig,ls,c,rs.
  (c = None ? → ls = [ ] ∨ rs = [ ]) → 
  tape_move ? (mk_tape sig ls c rs) R =
  mk_tape ? (option_cons ? c ls) (option_hd ? rs) (tail ? rs).
#sig * [ * [ * | #c * ] | #l0 #ls0 * [ *
[| #r0 #rs0 #H @False_ind cases (H (refl ??)) #H1 destruct (H1) ] | #c * ] ] 
normalize //
qed.

lemma sem_obj_to_cfg : obj_to_cfg ⊨  R_obj_to_cfg.
@(sem_seq_app FSUnialpha 2 ????? (sem_move_multi ? 2 cfg L ?)
   (sem_seq ??????
    (sem_if ??????????
     (sem_test_null_multi ?? obj ?)
      (sem_seq ?????? (accRealize_to_Realize … (sem_copy_step …))
       (sem_seq ?????? (sem_move_multi ? 2 cfg L ?)
        (sem_move_multi ? 2 obj L ?)))
      (sem_inject ???? cfg ? (sem_write FSUnialpha null)))
     (sem_seq ?????? (sem_inject ???? cfg ? (sem_move_to_end_l ?))
       (sem_move_multi ? 2 cfg R ?)))) //
#ta #tb *
#tc * whd in ⊢ (%→?); #Htc *
#td * *
[ * #te * * #Hcurtc #Hte
  * destruct (Hte) #te * *
  [ whd in ⊢ (%→%→?); * #x * #y * * -Hcurtc #Hcurtc1 #Hcurtc2 #Hte
    * #tf * whd in ⊢ (%→%→?); #Htf #Htd
    * #tg * * * whd in ⊢ (%→%→%→%→?); #Htg1 #Htg2 #Htg3 #Htb
    #c #ls #Hta1 %
    [ #lso #x0 #rso #Hta2 >Hta1 in Htc; >eq_mk_tape_rightof 
      whd in match (tape_move ???); #Htc
      cut (tg = change_vec ?? td (mk_tape ? [ ] (None ?) (reverse ? ls@[x])) cfg)
      [@daemon] -Htg1 -Htg2 -Htg3 #Htg destruct (Htg Htf Hte Htd Htc Htb)
      >change_vec_change_vec >change_vec_change_vec
      >change_vec_commute // >change_vec_change_vec
      >change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
      >change_vec_commute // >change_vec_change_vec
      >nth_change_vec // >nth_change_vec_neq [|@sym_not_eq //] 
      >nth_change_vec // >nth_change_vec_neq [|@sym_not_eq //]
      >change_vec_commute [|@sym_not_eq //] @eq_f3 //
      [ >Hta2 cases rso in Hta2; whd in match (tape_move_mono ???);
        [ #Hta2 whd in match (tape_move ???); <Hta2 @change_vec_same
        | #r1 #rs1 #Hta2 whd in match (tape_move ???); <Hta2 @change_vec_same ]
      | >tape_move_mk_tape_R [| #_ % %] >reverse_cons
        >nth_change_vec_neq in Hcurtc1; [|@sym_not_eq //] >Hta2
        normalize in ⊢ (%→?); #H destruct (H) %
      ]
    | #Hta2 >Htc in Hcurtc1; >nth_change_vec_neq [| @sym_not_eq //]
      >Hta2 #H destruct (H)
    ]
  | * #Hcurtc0 #Hte #_ #_ #c #ls #Hta1 >Hta1 in Htc; >eq_mk_tape_rightof
    whd in match (tape_move ???); #Htc >Htc in Hcurtc0; *
    [ >Htc in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //]
      #Hcurtc #Hcurtc0 >Hcurtc0 in Hcurtc; * #H @False_ind @H %
    | >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H) ]
  ]
| * #te * * #Hcurtc #Hte
  * whd in ⊢ (%→%→?); #Htd1 #Htd2
  * #tf * * * #Htf1 #Htf2 #Htf3 whd in ⊢ (%→?); #Htb
  #c #ls #Hta1 %
  [ #lso #x #rso #Hta2 >Htc in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //] 
    >Hta2 normalize in ⊢ (%→?); #H destruct (H)
  | #_ >Hta1 in Htc; >eq_mk_tape_rightof whd in match (tape_move ???); #Htc
    destruct (Hte) cut (td = change_vec ?? tc (midtape ? ls null []) cfg)
    [@daemon] -Htd1 -Htd2 #Htd
    -Htf1 cut (tf = change_vec ?? td (mk_tape ? [ ] (None ?) (reverse ? ls@[null])) cfg)
    [@daemon] -Htf2 -Htf3 #Htf destruct (Htf Htd Htc Htb)
    >change_vec_change_vec >change_vec_change_vec >change_vec_change_vec
    >change_vec_change_vec >change_vec_change_vec >nth_change_vec //
    >reverse_cons >tape_move_mk_tape_R /2/ ]
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
    (copy_step cfg obj FSUnialpha 2 ·
     mmove cfg FSUnialpha 2 L ·
     mmove obj FSUnialpha 2 L) 
     tc_true) ·
  inject_TM ? (move_to_end FSUnialpha L) 2 cfg ·
  mmove cfg FSUnialpha 2 R.
  
definition R_cfg_to_obj ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls) (None ?) [ ] → 
  (c = null → 
   t2 = change_vec ?? t1
         (mk_tape ? [ ] (option_hd FSUnialpha (reverse ? (c::ls))) 
           (tail ? (reverse ? (c::ls)))) cfg) ∧
  (c ≠ null → 
   t2 = change_vec ??
          (change_vec ?? t1
             (midtape ? (left ? (nth obj ? t1 (niltape ?))) c (right ? (nth obj ? t1 (niltape ?)))) obj)
          (mk_tape ? [ ] (option_hd ? (reverse ? (c::ls))) (tail ? (reverse ? (c::ls)))) cfg).

axiom sem_cfg_to_obj : cfg_to_obj ⊨  R_cfg_to_obj.
(*@(sem_seq_app FSUnialpha 2 ????? (sem_move_multi ? 2 cfg L ?)
   (sem_seq ??????
    (sem_if ??????????
     (sem_test_null_multi ?? obj ?)
      (sem_seq ?????? (accRealize_to_Realize … (sem_copy_step …))
       (sem_move_multi ? 2 cfg L ?))
      (sem_inject ???? cfg ? (sem_write FSUnialpha null)))
     (sem_seq ?????? (sem_inject ???? cfg ? (sem_move_to_end_l ?))
       (sem_move_multi ? 2 cfg R ?)))) //
#ta #tb *
#tc * whd in ⊢ (%→?); #Htc *
#td * *
[ * #te * * #Hcurtc #Hte
  * destruct (Hte) #te * *
  [ whd in ⊢ (%→%→?); * #x * #y * * -Hcurtc #Hcurtc1 #Hcurtc2 #Hte #Htd
    * #tf * * * whd in ⊢ (%→%→%→%→?); #Htf1 #Htf2 #Htf3 #Htb
    #c #ls #Hta1 %
    [ #lso #x0 #rso #Hta2 >Hta1 in Htc; >eq_mk_tape_rightof 
      whd in match (tape_move ???); #Htc
      cut (tf = change_vec ?? tc (mk_tape ? [ ] (None ?) (reverse ? ls@[x])) cfg)
      [@daemon] -Htf1 -Htf2 -Htf3 #Htf destruct (Htf Hte Htd Htc Htb)
      >change_vec_change_vec >change_vec_change_vec >change_vec_change_vec
      >nth_change_vec // >tape_move_mk_tape_R
      @daemon
    | #Hta2 >Htc in Hcurtc1; >nth_change_vec_neq [| @sym_not_eq //]
      >Hta2 #H destruct (H)
    ]
  | * #Hcurtc0 #Hte #_ #_ #c #ls #Hta1 >Hta1 in Htc; >eq_mk_tape_rightof
    whd in match (tape_move ???); #Htc >Htc in Hcurtc0; *
    [ >Htc in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //]
      #Hcurtc #Hcurtc0 >Hcurtc0 in Hcurtc; * #H @False_ind @H %
    | >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H) ]
  ]
| * #te * * #Hcurtc #Hte
  * whd in ⊢ (%→%→?); #Htd1 #Htd2
  * #tf * * * #Htf1 #Htf2 #Htf3 whd in ⊢ (%→?); #Htb
  #c #ls #Hta1 %
  [ #lso #x #rso #Hta2 >Htc in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //] 
    >Hta2 normalize in ⊢ (%→?); #H destruct (H)
  | #_ >Hta1 in Htc; >eq_mk_tape_rightof whd in match (tape_move ???); #Htc
    destruct (Hte) cut (td = change_vec ?? tc (midtape ? ls null []) cfg)
    [@daemon] -Htd1 -Htd2 #Htd
    -Htf1 cut (tf = change_vec ?? td (mk_tape ? [ ] (None ?) (reverse ? ls@[null])) cfg)
    [@daemon] -Htf2 -Htf3 #Htf destruct (Htf Htd Htc Htb)
    >change_vec_change_vec >change_vec_change_vec >change_vec_change_vec
    >change_vec_change_vec >change_vec_change_vec >nth_change_vec //
    >reverse_cons >tape_move_mk_tape_R /2/ ]
]
qed.
*)

(* macchina che muove il nastro obj a destra o sinistra a seconda del valore
   del current di prg, che codifica la direzione in cui ci muoviamo *)

definition char_to_move ≝ λc.match c with
  [ bit b ⇒ if b then R else L
  | _ ⇒ N].
  
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

definition restart_tape ≝ λi. 
  inject_TM ? (move_to_end FSUnialpha L) 2 i ·
  mmove i FSUnialpha 2 R. 

definition unistep ≝ 
  obj_to_cfg · match_m cfg prg FSUnialpha 2 · 
  restart_tape cfg · copy prg cfg FSUnialpha 2 ·
  cfg_to_obj · tape_move_obj · restart_tape prg.

(*
definition legal_tape ≝ λn,l,h,t.
  ∃state,char,table.
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[char]) →
  is_config n (bar::state@[char]) →  
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h → *)

definition list_of_tape ≝ λsig,t. 
  left sig t@option_cons ? (current ? t) (right ? t).

definition low_char' ≝ λc.
  match c with
  [ None ⇒ null 
  | Some b ⇒ if (is_bit b) then b else null
  ].
  
definition R_unistep ≝ λn,l,h.λt1,t2: Vector ? 3.
  ∀state,oldc,table.
  (* cfg *)
  nth cfg ? t1 (niltape ?) = midtape ? [ ] bar (state@[oldc]) →
  is_config n (bar::state@[oldc]) →  
  (* prg *)
  nth prg ? t1 (niltape ?) = midtape ? [ ] bar table →
  bar::table = table_TM n l h →
  (* obj *)
  only_bits (list_of_tape ? (nth obj ? t1 (niltape ?))) →
  let char ≝ low_char' (current ? (nth obj ? t1 (niltape ?))) in
  let conf ≝ (bar::state@[char]) in
  (∃ll,lr.bar::table = ll@conf@lr) → 
    ∃nstate,nchar,m,t. tuple_encoding n h t = (conf@nstate@[nchar;m]) ∧ 
    mem ? t l ∧
    t2 = 
      change_vec ??
        (change_vec ?? t1 (midtape ? [ ] bar (nstate@[nchar])) cfg)
        (tape_move_mono ? (nth obj ? t1 (niltape ?)) 〈Some ? nchar,char_to_move m〉) obj.
    
  
  
  
  
  