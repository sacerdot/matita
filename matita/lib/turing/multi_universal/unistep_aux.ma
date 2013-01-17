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
     mmove cfg FSUnialpha 2 L) 
    (inject_TM ? (write FSUnialpha null) 2 cfg)
     tc_true) ·
  inject_TM ? (move_to_end FSUnialpha L) 2 cfg ·
  mmove cfg FSUnialpha 2 R.
  
definition R_obj_to_cfg ≝ λt1,t2:Vector (tape FSUnialpha) 3.
  ∀c,ls.
  nth cfg ? t1 (niltape ?) = mk_tape FSUnialpha (c::ls) (None ?) [ ] → 
  (∀lso,x,rso.nth obj ? t1 (niltape ?) = midtape FSUnialpha lso x rso → 
   t2 = change_vec ?? t1 
         (mk_tape ? [ ] (option_hd ? (reverse ? (c::ls))) (tail ? (reverse ? (c::ls)))) cfg) ∧
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
       
lemma wsem_copy : ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊫ R_copy src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_copy_step src dst sig n Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ whd in ⊢ (%→?); * #Hnone #Hout %
  [#_ @Hout
  |#ls #x #x0 #rs #ls0 #rs0 #Hsrc1 #Hdst1 @False_ind cases Hnone
    [>Hsrc1 normalize #H destruct (H) | >Hdst1 normalize #H destruct (H)]
  ]
|#tc #td * #x * #y * * #Hcx #Hcy #Htd #Hstar #IH #He lapply (IH He) -IH *
 #IH1 #IH2 %
  [* [>Hcx #H destruct (H) | >Hcy #H destruct (H)]
  |#ls #x' #y' #rs #ls0 #rs0 #Hnth_src #Hnth_dst
   >Hnth_src in Hcx; whd in ⊢ (??%?→?); #H destruct (H)
   >Hnth_dst in Hcy; whd in ⊢ (??%?→?); #H destruct (H)
   >Hnth_src in Htd; >Hnth_dst -Hnth_src -Hnth_dst
   cases rs
    [(* the source tape is empty after the move *)
     #Htd lapply (IH1 ?) 
      [%1 >Htd >nth_change_vec_neq [2:@(not_to_not … Hneq) //] >nth_change_vec //]
     #Hout (* whd in match (tape_move ???); *) %1 %{([])} %{rs0} % 
      [% [// | // ] 
      |whd in match (reverse ??); whd in match (reverse ??);
       >Hout >Htd @eq_f2 // cases rs0 //
      ]
    |#c1 #tl1 cases rs0
      [(* the dst tape is empty after the move *)
       #Htd lapply (IH1 ?) [%2 >Htd >nth_change_vec //] 
       #Hout (* whd in match (tape_move ???); *) %2 %{[ ]} %{(c1::tl1)} % 
        [% [// | // ] 
        |whd in match (reverse ??); whd in match (reverse ??);
         >Hout >Htd @eq_f2 // 
        ]
      |#c2 #tl2 whd in match (tape_move_mono ???); whd in match (tape_move_mono ???);
       #Htd
       cut (nth src (tape sig) td (niltape sig)=midtape sig (x::ls) c1 tl1)
         [>Htd >nth_change_vec_neq [2:@(not_to_not … Hneq) //] @nth_change_vec //]
       #Hsrc_td
       cut (nth dst (tape sig) td (niltape sig)=midtape sig (x::ls0) c2 tl2)
         [>Htd @nth_change_vec //]
       #Hdst_td cases (IH2 … Hsrc_td Hdst_td) -Hsrc_td -Hdst_td
        [* #rs01 * #rs02 * * #H1 #H2 #H3 %1
         %{(c2::rs01)} %{rs02} % [% [@eq_f //|normalize @eq_f @H2]]
         >Htd in H3; >change_vec_commute // >change_vec_change_vec
         >change_vec_commute [2:@(not_to_not … Hneq) //] >change_vec_change_vec 
         #H >reverse_cons >associative_append >associative_append @H 
        |* #rs11 * #rs12 * * #H1 #H2 #H3 %2
         %{(c1::rs11)} %{rs12} % [% [@eq_f //|normalize @eq_f @H2]]
         >Htd in H3; >change_vec_commute // >change_vec_change_vec
         >change_vec_commute [2:@(not_to_not … Hneq) //] >change_vec_change_vec 
         #H >reverse_cons >associative_append >associative_append @H 
        ]
      ]
    ]
  ]
qed.
     
 
lemma terminate_copy :  ∀src,dst,sig,n,t.
  src ≠ dst → src < S n → dst < S n → copy src dst sig n ↓ t.
#src #dst #sig #n #t #Hneq #Hsrc #Hdts
@(terminate_while … (sem_copy_step …)) //
<(change_vec_same … t src (niltape ?))
cases (nth src (tape sig) t (niltape ?))
[ % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
|2,3: #a0 #al0 % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * #y * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #_ >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * #y0 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * #y * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcur
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_copy : ∀src,dst,sig,n.
  src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n ⊨ R_copy src dst sig n.
#i #j #sig #n #Hneq #Hi #Hj @WRealize_to_Realize [/2/| @wsem_copy // ]
qed.
