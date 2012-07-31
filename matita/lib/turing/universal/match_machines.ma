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


include "turing/universal/tuples.ma".
include "turing/universal/marks.ma".

(*
l0 x* a l1 x0* a0 l2 ------> l0 x a* l1 x0 a0* l2
   ^                               ^

if current (* x *) = #
   then 
   else if x = 0
      then move_right; ----
           adv_to_mark_r;
           if current (* x0 *) = 0
              then advance_mark ----
                   adv_to_mark_l;
                   advance_mark
              else STOP
      else x = 1 (* analogo *)

*)


(*
   MARK NEXT TUPLE machine
   (partially axiomatized)
   
   marks the first character after the first bar (rightwards)
 *)
 
definition mark_next_tuple ≝ 
  adv_to_mark_r ? bar_or_grid ·
     (ifTM ? (test_char ? (λc:STape.is_bar (\fst c)))
       (move_right_and_mark ?) (nop ?) tc_true).

definition R_mark_next_tuple ≝ 
  λt1,t2.
    ∀ls,c,rs1,rs2.
    (* c non può essere un separatore ... speriamo *)
    t1 = midtape STape ls c (rs1@〈grid,false〉::rs2) → 
    no_marks rs1 → no_grids rs1 → bar_or_grid c = false → 
    (∃rs3,rs4,d,b.rs1 = rs3 @ 〈bar,false〉 :: rs4 ∧
      no_bars rs3 ∧
      Some ? 〈d,b〉 = option_hd ? (rs4@〈grid,false〉::rs2) ∧
      t2 = midtape STape (〈bar,false〉::reverse ? rs3@c::ls) 〈d,true〉 (tail ? (rs4@〈grid,false〉::rs2)))
    ∨
    (no_bars rs1 ∧ t2 = midtape ? (reverse ? rs1@c::ls) 〈grid,false〉 rs2).
     
axiom daemon :∀P:Prop.P.

axiom tech_split :
  ∀A:DeqSet.∀f,l.
   (∀x.memb A x l = true → f x = false) ∨
   (∃l1,c,l2.f c = true ∧ l = l1@c::l2 ∧ ∀x.memb ? x l1 = true → f x = false).
(*#A #f #l elim l
[ % #x normalize #Hfalse *)
     
theorem sem_mark_next_tuple :
  Realize ? mark_next_tuple R_mark_next_tuple.
#intape 
lapply (sem_seq ? (adv_to_mark_r ? bar_or_grid)
         (ifTM ? (test_char ? (λc:STape.is_bar (\fst c))) (move_right_and_mark ?) (nop ?) tc_true) ????)
[@sem_if [5: // |6: @sem_move_right_and_mark |7: // |*:skip]
| //
|||#Hif cases (Hif intape) -Hif
   #j * #outc * #Hloop * #ta * #Hleft #Hright
   @(ex_intro ?? j) @ex_intro [|% [@Hloop] ]
   -Hloop
   #ls #c #rs1 #rs2 #Hrs #Hrs1 #Hrs1' #Hc
   cases (proj2 ?? Hleft … Hrs)
   [ * #Hfalse >Hfalse in Hc; #Htf destruct (Htf)
   | * * #_ #Hta #_ cases (tech_split STape (λc.is_bar (\fst c)) rs1)
     [ #H1 %2 % [@H1]
      lapply (Hta rs1 〈grid,false〉 rs2 (refl ??) ? ?)
       [ * #x #b #Hx whd in ⊢ (??%?); >(Hrs1' … Hx) >(H1 … Hx) %
       | %
       | -Hta #Hta cases Hright
         [ * #tb * whd in ⊢ (%→?); * * #c1 * >Hta 
          whd in ⊢ ((??%?)→?); #H destruct (H) whd in ⊢ ((??%?)→?); #H destruct
         | * #tb * whd in ⊢ (%→?); * #_ #Htb >Htb >Hta 
           whd in ⊢ (%→?); #H @H
         ]
       ]
    |* #rs3 * #c0 * #rs4 * * #Hc0 #Hsplit #Hrs3
     % @(ex_intro ?? rs3) @(ex_intro ?? rs4)
     lapply (Hta rs3 c0 (rs4@〈grid,false〉::rs2) ???)
      [#x #Hrs3' whd in ⊢ (??%?); >Hsplit in Hrs1;>Hsplit in Hrs3;
       #Hrs3 #Hrs1 >(Hrs1 …) [| @memb_append_l1 @Hrs3'|]
       >(Hrs3 … Hrs3') @Hrs1' >Hsplit @memb_append_l1 //
      |whd in ⊢ (??%?); >Hc0 %
      |>Hsplit >associative_append % 
      ]-Hta #Hta
     cases Hright -Hright 
      [* whd in ⊢ (%→?); #tb * * * #c1 * >Hta -Hta 
       whd in ⊢ (??%?→?); #H destruct (H) #Hc1 #Htb
       whd in ⊢ (%→?); #Houtc 
       cut (c1=〈bar,false〉)
        [lapply Hc1 lapply Hsplit cases c1 #c1l #c1r #Hsplit
         cases c1l normalize 
          [#b #H destruct |2,3,5:#H destruct] 
           #_ @eq_f @(Hrs1 … 〈c1l,c1r〉) >Hsplit @memb_append_l2 @memb_hd]
       #Hcut lapply Hsplit -Hsplit
       cases rs4 in Htb;
        [#Htb lapply(Houtc … Htb) -Houtc #Houtc #Hsplit
         @(ex_intro ?? grid) @(ex_intro ?? false) % 
          [% [ % [<Hcut @Hsplit |@Hrs3 ] | % ] 
          |>Houtc >Hcut % 
          ]
        |* #r5l #r5r #rs5 #Htb
         lapply(Houtc … Htb) -Houtc #Houtc #Hsplit
         @(ex_intro ?? r5l) @(ex_intro ?? r5r) % 
          [%[%[<Hcut @Hsplit| @Hrs3] | % ]
          |>Houtc >Hcut % 
          ]
        ]
      |* whd in ⊢ (%→?); #tb * * 
       #H @False_ind >Hta in H; #H lapply(H c0 (refl …))
       >Hc0 #H destruct
      ]
    ]
  ]
]
qed.

definition init_current_on_match ≝ 
  move_l ? · adv_to_mark_l ? (λc:STape.is_grid (\fst c)) · move_r ? · mark ?.
          
definition R_init_current_on_match ≝ λt1,t2.
  ∀l1,l2,c,rs. no_grids l1 → is_grid c = false → 
  t1 = midtape STape (l1@〈c,false〉::〈grid,false〉::l2)  〈grid,false〉 rs → 
  t2 = midtape STape (〈grid,false〉::l2) 〈c,true〉 ((reverse ? l1)@〈grid,false〉::rs).

lemma sem_init_current_on_match : 
  Realize ? init_current_on_match R_init_current_on_match.
#intape 
cases (sem_seq ????? (sem_move_l ?)
        (sem_seq ????? (sem_adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
           (sem_seq ????? (sem_move_r ?) (sem_mark ?))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #l2 #c #rs #Hl1 #Hc #Hintape
cases HR -HR #ta * whd in ⊢ (%→?); #Hta lapply (Hta … Hintape) -Hta -Hintape 
generalize in match Hl1; cases l1
  [#Hl1 whd in ⊢ ((???(??%%%))→?); #Hta
   * #tb * whd in ⊢ (%→?); #Htb cases (Htb … Hta) -Hta
    [* >Hc #Htemp destruct (Htemp) ]
   * #_ #Htc lapply (Htc [ ] 〈grid,false〉 ? (refl ??) (refl …) Hl1) 
   whd in ⊢ ((???(??%%%))→?); -Htc #Htc
   * #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htc -Htd 
   whd in ⊢ ((???(??%%%))→?); #Htd
   whd in ⊢ (%→?); #Houtc lapply (Houtc … Htd) -Houtc #Houtc
   >Houtc % 
  |#d #tl #Htl whd in ⊢ ((???(??%%%))→?); #Hta
   * #tb * whd in ⊢ (%→?); #Htb cases (Htb … Hta) -Htb
    [* >(Htl … (memb_hd …)) #Htemp destruct (Htemp)]    
   * #Hd >append_cons #Htb lapply (Htb … (refl ??) (refl …) ?)
    [#x #membx cases (memb_append … membx) -membx #membx
      [@Htl @memb_cons @membx | >(memb_single … membx) @Hc]]-Htb  #Htb
   * #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htb -Htc 
   >reverse_append >associative_append whd in ⊢ ((???(??%%%))→?); #Htc
   whd in ⊢ (%→?); #Houtc lapply (Houtc … Htc) -Houtc #Houtc 
   >Houtc >reverse_cons >associative_append % 
  ]
qed.   

(*
definition init_current_gen ≝ 
  seq ? (adv_to_mark_l ? (is_marked ?))
    (seq ? (clear_mark ?)
       (seq ? (move_l ?)
         (seq ? (adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
            (seq ? (move_r ?) (mark ?))))).
          
definition R_init_current_gen ≝ λt1,t2.
  ∀l1,c,l2,b,l3,c1,rs,c0,b0. no_marks l1 → no_grids l2 →
  Some ? 〈c0,b0〉 = option_hd ? (reverse ? (〈c,true〉::l2)) → 
  t1 = midtape STape (l1@〈c,true〉::l2@〈grid,b〉::l3) 〈c1,false〉 rs → 
  t2 = midtape STape (〈grid,b〉::l3) 〈c0,true〉
        ((tail ? (reverse ? (l1@〈c,false〉::l2))@〈c1,false〉::rs)).

lemma sem_init_current_gen : Realize ? init_current_gen R_init_current_gen.
#intape 
cases (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?))
        (sem_seq ????? (sem_clear_mark ?)
          (sem_seq ????? (sem_move_l ?)
            (sem_seq ????? (sem_adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
              (sem_seq ????? (sem_move_r ?) (sem_mark ?))))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop] -Hloop
#l1 #c #l2 #b #l3 #c1 #rs #c0 #b0 #Hl1 #Hl2 #Hc #Hintape
cases HR -HR #ta * whd in ⊢ (%→?); #Hta cases (Hta … Hintape) -Hta -Hintape
  [ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
* #_ #Hta lapply (Hta l1 〈c,true〉 ? (refl ??) ??) [@Hl1|%] -Hta #Hta
* #tb * whd in ⊢ (%→?); #Htb lapply (Htb … Hta) -Htb -Hta #Htb 
* #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htc -Htb 
generalize in match Hc; generalize in match Hl2; cases l2
  [#_ whd in ⊢ ((???%)→?); #Htemp destruct (Htemp) 
   whd in ⊢ ((???(??%%%))→?); #Htc
   * #td * whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd
    [2: * whd in ⊢ (??%?→?); #Htemp destruct (Htemp) ]
   * #_ #Htd >Htd in Htc; -Htd #Htd
   * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Htd
   >reverse_append >reverse_cons 
   whd in ⊢ ((???(??%%%))→?); #Hte
   whd in ⊢ (%→?); #Houtc lapply (Houtc … Hte) -Houtc -Hte #Houtc
   >Houtc %
  |#d #tl #Htl #Hc0 whd in ⊢ ((???(??%%%))→?); #Htc
   * #td * whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd
    [* >(Htl … (memb_hd …)) whd in ⊢ (??%?→?); #Htemp destruct (Htemp)]    
   * #Hd #Htd lapply (Htd … (refl ??) (refl ??) ?)
    [#x #membx @Htl @memb_cons @membx] -Htd #Htd
   * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Htd
   >reverse_append >reverse_cons >reverse_cons
   >reverse_cons in Hc0; >reverse_cons cases (reverse ? tl)
     [normalize in ⊢ (%→?); #Hc0 destruct (Hc0) #Hte 
      whd in ⊢ (%→?); #Houtc lapply (Houtc … Hte) -Houtc -Hte #Houtc
      >Houtc %
     |* #c2 #b2 #tl2 normalize in ⊢ (%→?); #Hc0 destruct (Hc0)  
      whd in ⊢ ((???(??%%%))→?); #Hte 
      whd in ⊢ (%→?); #Houtc lapply (Houtc … Hte) -Houtc -Hte #Houtc
      >Houtc >associative_append >associative_append >associative_append %
     ]
   ]
qed.
*)

definition init_current ≝ 
  adv_to_mark_l ? (is_marked ?) ·clear_mark ? ·
    adv_to_mark_l ? (λc:STape.is_grid (\fst c)) · move_r ? · mark ?.
          
definition R_init_current ≝ λt1,t2.
  ∀l1,c,l2,b,l3,c1,rs,c0,b0. no_marks l1 → no_grids l2 → is_grid c = false → 
  Some ? 〈c0,b0〉 = option_hd ? (reverse ? (〈c,true〉::l2)) → 
  t1 = midtape STape (l1@〈c,true〉::l2@〈grid,b〉::l3) 〈c1,false〉 rs → 
  t2 = midtape STape (〈grid,b〉::l3) 〈c0,true〉
        ((tail ? (reverse ? (l1@〈c,false〉::l2))@〈c1,false〉::rs)).

lemma sem_init_current : Realize ? init_current R_init_current.
#intape 
cases (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?))
        (sem_seq ????? (sem_clear_mark ?)
           (sem_seq ????? (sem_adv_to_mark_l ? (λc:STape.is_grid (\fst c)))
             (sem_seq ????? (sem_move_r ?) (sem_mark ?)))) intape)
#k * #outc * #Hloop #HR 
@(ex_intro ?? k) @(ex_intro ?? outc) % [@Hloop]
cases HR -HR #ta * whd in ⊢ (%→?); #Hta 
* #tb * whd in ⊢ (%→?); #Htb 
* #tc * whd in ⊢ (%→?); #Htc 
* #td * whd in ⊢ (%→%→?); #Htd #Houtc
#l1 #c #l2 #b #l3 #c1 #rs #c0 #b0 #Hl1 #Hl2 #Hc #Hc0 #Hintape
cases (Hta … Hintape) [ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
-Hta * #_ #Hta lapply (Hta l1 〈c,true〉 ? (refl ??) ??) [@Hl1|%]
-Hta #Hta lapply (Htb … Hta) -Htb #Htb cases (Htc … Htb) [ >Hc -Hc * #Hc destruct (Hc) ] 
-Htc * #_ #Htc lapply (Htc … (refl ??) (refl ??) ?) [@Hl2]
-Htc #Htc lapply (Htd … Htc) -Htd
>reverse_append >reverse_cons 
>reverse_cons in Hc0; cases (reverse … l2)
[ normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
  #Htd >(Houtc … Htd) %
| * #c2 #b2 #tl2 normalize in ⊢ (%→?);
  #Hc0 #Htd >(Houtc … Htd)
  whd in ⊢ (???%); destruct (Hc0)
  >associative_append >associative_append %
]
qed.

definition match_tuple_step ≝ 
  ifTM ? (test_char ? (λc:STape.¬ is_grid (\fst c))) 
   (single_finalTM ? 
     (compare ·
      (ifTM ? (test_char ? (λc:STape.is_grid (\fst c)))
        (nop ?)
        (mark_next_tuple ·
           (ifTM ? (test_char ? (λc:STape.is_grid (\fst c)))
             (mark ?) (move_l ? · init_current) tc_true)) tc_true)))
    (nop ?) tc_true.

definition R_match_tuple_step_true ≝ λt1,t2.
  ∀ls,cur,rs.t1 = midtape STape ls cur rs → 
  \fst cur ≠ grid ∧ 
  (∀ls0,c,l1,l2,c1,l3,l4,rs0,n.
   only_bits_or_nulls l1 → no_marks l1 (* → no_grids l2 *) → 
   bit_or_null c = true → bit_or_null c1 = true →
   only_bits_or_nulls l3 → S n = |l1| → |l1| = |l3| →
   table_TM (S n) (l2@〈c1,false〉::l3@〈comma,false〉::l4) → 
   ls = 〈grid,false〉::ls0 → cur = 〈c,true〉 → 
   rs = l1@〈grid,false〉::l2@〈c1,true〉::l3@〈comma,false〉::l4@〈grid,false〉::rs0 → 
   (* facciamo match *)
   (〈c,false〉::l1 = 〈c1,false〉::l3 ∧
   t2 = midtape ? (reverse ? l1@〈c,false〉::〈grid,false〉::ls0) 〈grid,false〉
         (l2@〈c1,false〉::l3@〈comma,true〉::l4@〈grid,false〉::rs0))
   ∨
   (* non facciamo match e marchiamo la prossima tupla *)
   (〈c,false〉::l1 ≠ 〈c1,false〉::l3 ∧
    ∃c2,l5,l6.l4 = l5@〈bar,false〉::〈c2,false〉::l6 ∧
    (* condizioni su l5 l6 l7 *)
    t2 = midtape STape (〈grid,false〉::ls0) 〈c,true〉 
          (l1@〈grid,false〉::l2@〈c1,false〉::l3@〈comma,false〉::
           l5@〈bar,false〉::〈c2,true〉::l6@〈grid,false〉::rs0))
   ∨  
   (* non facciamo match e non c'è una prossima tupla:
      non specifichiamo condizioni sul nastro di output, perché
      non eseguiremo altre operazioni, quindi il suo formato non ci interessa *)
   (〈c,false〉::l1 ≠ 〈c1,false〉::l3 ∧ no_bars l4 ∧ current ? t2 = Some ? 〈grid,true〉)).  
  
definition R_match_tuple_step_false ≝ λt1,t2.
  ∀ls,c,rs.t1 = midtape STape ls c rs → is_grid (\fst c) = true ∧ t2 = t1.
  
include alias "basics/logic.ma". 

(*
lemma eq_f4: ∀A1,A2,A3,A4,B.∀f:A1 → A2 →A3 →A4 →B.
  ∀x1,x2,x3,x4,y1,y2,y3,y4. x1 = y1 → x2 = y2 →x3=y3 →x4 = y4 →   
    f x1 x2 x3 x4 = f y1 y2 y3 y4.
//
qed-. *)

lemma some_option_hd: ∀A.∀l:list A.∀a.∃b.
  Some ? b = option_hd ? (l@[a]) .
#A #l #a cases l normalize /2/
qed.

axiom tech_split2 : ∀A,l1,l2,l3,l4,x. 
  memb A x l1 = false → memb ? x l3 = false → 
  l1@x::l2 = l3@x::l4 → l1 = l3 ∧ l2 = l4.
  
axiom injective_append : ∀A,l.injective … (λx.append A x l).

lemma sem_match_tuple_step: 
    accRealize ? match_tuple_step (inr … (inl … (inr … start_nop))) 
    R_match_tuple_step_true R_match_tuple_step_false.
@(acc_sem_if_app … (sem_test_char ? (λc:STape.¬ is_grid (\fst c))) …
  (sem_seq … sem_compare
    (sem_if … (sem_test_char ? (λc:STape.is_grid (\fst c)))
      (sem_nop …)
        (sem_seq … sem_mark_next_tuple 
           (sem_if … (sem_test_char ? (λc:STape.is_grid (\fst c)))
             (sem_mark ?) (sem_seq … (sem_move_l …) (sem_init_current …))))))
  (sem_nop ?) …)
[(* is_grid: termination case *)
 2:#t1 #t2 #t3 whd in ⊢ (%→?); #H #H1 whd #ls #c #rs #Ht1
  cases (H c ?) [2: >Ht1 %] #Hgrid #Heq %
    [@injective_notb @Hgrid | <Heq @H1]
|#tapea #tapeout #tapeb whd in ⊢ (%→?); #Hcur
 * #tapec * whd in ⊢ (%→?); #Hcompare #Hor 
 #ls #cur #rs #Htapea >Htapea in Hcur; #Hcur cases (Hcur ? (refl ??)) 
 -Hcur #Hcur #Htapeb %
 [ % #Hfalse >Hfalse in Hcur; normalize #Hfalse1 destruct (Hfalse1)]
 #ls0 #c #l1 #l2 #c1 #l3 #l4 #rs0 #n #Hl1bitnull #Hl1marks #Hc #Hc1 #Hl3 #eqn
 #eqlen #Htable #Hls #Hcur #Hrs -Htapea >Hls in Htapeb; >Hcur >Hrs #Htapeb
 cases (Hcompare … Htapeb) -Hcompare -Htapeb * #_ #_ #Hcompare
 cases (Hcompare c c1 l1 l3 l2 (l4@〈grid,false〉::rs0) eqlen Hl1bitnull Hl3 Hl1marks … (refl …) Hc ?)  
 -Hcompare 
   [* #Htemp destruct (Htemp) #Htapec %1 % % [%]
    >Htapec in Hor; -Htapec *
     [2: * #t3 * whd in ⊢ (%→?); #H @False_ind
      cases (H … (refl …)) whd in ⊢ ((??%?)→?); #H destruct (H)
     |* #taped * whd in ⊢ (%→?); #Htaped cases (Htaped ? (refl …)) -Htaped *
      #Htaped whd in ⊢ (%→?); #Htapeout >Htapeout >Htaped
      %
     ]
   |* #la * #c' * #d' * #lb * #lc * * * #H1 #H2 #H3 #Htapec 
    cut (〈c,false〉::l1 ≠ 〈c1,false〉::l3) 
      [>H2 >H3 elim la
        [@(not_to_not …H1) normalize #H destruct % 
        |#x #tl @not_to_not normalize #H destruct // 
        ]
      ] #Hnoteq
    cut (bit_or_null d' = true) 
      [cases la in H3;
        [normalize in ⊢ (%→?); #H destruct //
        |#x #tl #H @(Hl3 〈d',false〉)
         normalize in H; destruct @memb_append_l2 @memb_hd
        ] 
      ] #Hd'
    >Htapec in Hor; -Htapec *
     [* #taped * whd in ⊢ (%→?); #H @False_ind
      cases (H … (refl …)) >(bit_or_null_not_grid ? Hd') #Htemp destruct (Htemp)
     |* #taped * whd in ⊢ (%→?); #H cases (H … (refl …)) -H #_
      #Htaped * #tapee * whd in ⊢ (%→?); #Htapee  
      <(associative_append ? lc (〈comma,false〉::l4)) in Htaped; #Htaped
      cases (Htapee … Htaped ???) -Htaped -Htapee 
       [* #rs3 * * (* we proceed by cases on rs4 *) 
         [(* rs4 is empty : the case is absurd since the tape
            cannot end with a bar *)
          * #d * #b * * * #Heq1 @False_ind 
          cut (∀A,l1,l2.∀a:A. a::l1@l2=(a::l1)@l2) [//] #Hcut 
          >Hcut in Htable; >H3 >associative_append
          normalize >Heq1 <associative_append >Hcut
          <associative_append #Htable @(absurd … Htable) 
          @last_of_table
         |(* rs4 not empty *)
          * #d2 #b2 #rs3' * #d  * #b * * * #Heq1 #Hnobars
          cut (memb STape 〈d2,b2〉 (l2@〈c1,false〉::l3@〈comma,false〉::l4) = true)
            [@memb_append_l2
             cut (∀A,l1,l2.∀a:A. a::l1@l2=(a::l1)@l2) [//] #Hcut
             >Hcut >H3 >associative_append @memb_append_l2 
             @memb_cons >Heq1 @memb_append_l2 @memb_cons @memb_hd] #d2intable
          cut (is_grid d2 = false) 
            [@(no_grids_in_table … Htable … 〈d2,b2〉 d2intable)] #Hd2
          cut (b2 = false) 
            [@(no_marks_in_table … Htable … 〈d2,b2〉 d2intable)] #Hb2 
          >Hb2 in Heq1; #Heq1 -Hb2 -b2
          whd in ⊢ ((???%)→?); #Htemp destruct (Htemp) #Htapee >Htapee -Htapee *
           [(* we know current is not grid *)
            * #tapef * whd in ⊢ (%→?); #Htapef 
            cases (Htapef … (refl …)) >Hd2 #Htemp destruct (Htemp) 
           |* #tapef * whd in ⊢ (%→?); #Htapef 
            cases (Htapef … (refl …)) #_ -Htapef #Htapef
            * #tapeg >Htapef -Htapef * 
            (* move_l *)
            whd in ⊢ (%→?); 
            #H lapply (H … (refl …)) whd in ⊢ (???%→?); -H  #Htapeg
            >Htapeg -Htapeg
            (* init_current *)
             whd in ⊢ (%→?); #Htapeout
             cases (some_option_hd ? (reverse ? (reverse ? la)) 〈c',true〉)
             * #c00 #b00 #Hoption
             lapply 
              (Htapeout (reverse ? rs3 @〈d',false〉::reverse ? la@reverse ? l2@(〈grid,false〉::reverse ? lb))
              c' (reverse ? la) false ls0 bar (〈d2,true〉::rs3'@〈grid,false〉::rs0) c00 b00 ?????) -Htapeout
               [whd in ⊢ (??(??%??)?); @eq_f3 [2:%|3: %]
                >associative_append 
                 generalize in match (〈c',true〉::reverse ? la@〈grid,false〉::ls0); #l
                whd in ⊢ (???(???%)); >associative_append >associative_append % 
               |>reverse_cons @Hoption
               |cases la in H2; 
                 [normalize in ⊢ (%→?); #Htemp destruct (Htemp) 
                  @bit_or_null_not_grid @Hc
                 |#x #tl normalize in ⊢ (%→?); #Htemp destruct (Htemp)
                  @bit_or_null_not_grid @(Hl1bitnull 〈c',false〉) @memb_append_l2 @memb_hd
                 ]
               |cut (only_bits_or_nulls (la@(〈c',false〉::lb)))
                 [<H2 whd #c0 #Hmemb cases (orb_true_l … Hmemb)
                   [#eqc0 >(\P eqc0) @Hc |@Hl1bitnull]
                 |#Hl1' #x #Hx @bit_or_null_not_grid @Hl1'
                  @memb_append_l1 @daemon
                 ]
               |@daemon] #Htapeout % %2 % //
            @(ex_intro … d2)
            cut (∃rs32.rs3 = lc@〈comma,false〉::rs32) 
                 [ (*cases (tech_split STape (λc.c == 〈bar,false〉) l4)
                  [
                  | * #l41 * * #cbar #bfalse * #l42 * * #Hbar #Hl4 #Hl41
                    @(ex_intro ?? l41) >Hl4 in Heq1; #Heq1
                
                cut (sublist … lc l3)
                  [ #x #Hx cases la in H3;
                    [ normalize #H3 destruct (H3) @Hx
                    | #p #la' normalize #Hla' destruct (Hla')
                      @memb_append_l2 @memb_cons @Hx ] ] #Hsublist*)
                @daemon]
                * #rs32 #Hrs3
                (* cut 
                (〈c1,false〉::l3@〈comma,false〉::l4= la@〈d',false〉::rs3@〈bar,false〉::〈d2,b2〉::rs3')
                [@daemon] #Hcut *)
                cut (l4=rs32@〈bar,false〉::〈d2,false〉::rs3')
                [ >Hrs3 in Heq1; @daemon ] #Hl4
                @(ex_intro … rs32) @(ex_intro … rs3') % [@Hl4]
                >Htapeout @eq_f2
                   [(* by Hoption, H2 *) @daemon
                   |(*>Hrs3 *)>append_cons
                    > (?:l1@〈grid,false〉::l2@〈c1,false〉::l3@〈comma,false〉::rs32@〈bar,false〉::〈d2,true〉::rs3'@〈grid,false〉::rs
                        = (l1@〈grid,false〉::l2@〈c1,false〉::l3@〈comma,false〉::rs32@[〈bar,false〉])@〈d2,true〉::rs3'@〈grid,false〉::rs)
                    [|>associative_append normalize 
                      >associative_append normalize
                      >associative_append normalize
                      >associative_append normalize
                       % ]
                    >reverse_append >reverse_append >reverse_cons
                    >reverse_reverse >reverse_cons >reverse_reverse
                    >reverse_append >reverse_append >reverse_cons
                    >reverse_reverse >reverse_reverse >reverse_reverse
                    >(?:(la@[〈c',false〉])@((((lb@[〈grid,false〉])@l2)@la)@[〈d',false〉])@rs3
                       =((la@〈c',false〉::lb)@([〈grid,false〉]@l2@la@[〈d',false〉]@rs3)))
                    [|>associative_append >associative_append 
                      >associative_append >associative_append >associative_append
                      >associative_append % ]
                    <H2 normalize in ⊢ (??%?); >Hrs3
                    >associative_append >associative_append normalize
                    >associative_append >associative_append
                    @eq_f @eq_f @eq_f
                    >(?:la@(〈d',false〉::lc@〈comma,false〉::rs32)@〈bar,false〉::〈d2,true〉::rs3'@〈grid,false〉::rs0 = 
                        (la@〈d',false〉::lc)@〈comma,false〉::rs32@〈bar,false〉::〈d2,true〉::rs3'@〈grid,false〉::rs0 )
                    [| >associative_append normalize >associative_append % ]
                    <H3 %
                   ]
                 ]
              ]
       |* #Hnobars #Htapee >Htapee -Htapee *
         [whd in ⊢ (%→?); * #tapef * whd in ⊢ (%→?); #Htapef
          cases (Htapef … (refl …)) -Htapef #_ #Htapef >Htapef -Htapef
          whd in ⊢ (%→?); #Htapeout %2 % 
          [% [//] whd #x #Hx @Hnobars @memb_append_l2 @memb_cons //
          | >(Htapeout … (refl …)) % ]
         |whd in ⊢ (%→?); * #tapef * whd in ⊢ (%→?); #Htapef
          cases (Htapef … (refl …)) -Htapef 
          whd in ⊢ ((??%?)→?); #Htemp destruct (Htemp) 
         ]
       |(* no marks in table *)
        #x #membx @(no_marks_in_table … Htable) 
        @memb_append_l2
        cut (∀A,l1,l2.∀a:A. a::l1@l2=(a::l1)@l2) [//] #Hcut >Hcut
        >H3 >associative_append @memb_append_l2 @memb_cons @membx
       |(* no grids in table *)
        #x #membx @(no_grids_in_table … Htable) 
        @memb_append_l2
        cut (∀A,l1,l2.∀a:A. a::l1@l2=(a::l1)@l2) [//] #Hcut >Hcut
        >H3 >associative_append @memb_append_l2 @memb_cons @membx
       |whd in ⊢ (??%?); >(bit_or_null_not_grid … Hd') >(bit_or_null_not_bar … Hd') %
       ]
     ]
   |#x #membx @(no_marks_in_table … Htable) 
    @memb_append_l2 @memb_cons @memb_append_l1 @membx 
   |#x #membx @(no_marks_in_table … Htable) 
    @memb_append_l1 @membx
   |%
   ]
 ]
qed.

(* 
  MATCH TUPLE

  scrolls through the tuples in the transition table until one matching the
  current configuration is found
*)

definition match_tuple ≝  whileTM ? match_tuple_step (inr … (inl … (inr … start_nop))).

lemma is_grid_true : ∀c.is_grid c = true → c = grid.
* normalize [ #b ] #H // destruct (H)
qed.

(* possible variante ? 
definition weakR_match_tuple ≝ λt1,t2.
  (∀ls,cur,rs,b. t1 = midtape STape ls 〈grid,b〉 rs → t2 = t1) ∧
  (∀c,l1,c1,l2,l3,ls0,rs0,n.
  t1 = midtape STape (〈grid,false〉::ls0) 〈bit c,true〉 rs 
    (l1@〈grid,false〉::l2@〈bit c1,true〉::l3@〈grid,false〉::rs0) → 
  only_bits_or_nulls l1 → no_marks l1 → S n = |l1| →
  table_TM (S n) (l2@〈c1,false〉::l3) → 
  (* facciamo match *)
  (∃l4,newc,mv,l5.
   〈c1,false〉::l3 = l4@〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l5 ∧
   t2 = midtape ? (reverse ? l1@〈c,false〉::〈grid,false〉::ls0) 〈grid,false〉
        (l2@l4@〈c,false〉::l1@〈comma,true〉::newc@〈comma,false〉::mv::l5@
        〈grid,false〉::rs0))
  ∨
  (* non facciamo match su nessuna tupla;
     non specifichiamo condizioni sul nastro di output, perché
     non eseguiremo altre operazioni, quindi il suo formato non ci interessa *)
  (current ? t2 = Some ? 〈grid,true〉 ∧
   ∀l4,newc,mv,l5.
   〈c1,false〉::l3 ≠ l4@〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l5)).  
*) 

definition R_match_tuple0 ≝ λt1,t2.
  ∀ls,cur,rs.
  t1 = midtape STape ls cur rs → 
  (is_grid (\fst cur) = true → t2 = t1) ∧
  (∀c,l1,c1,l2,l3,ls0,rs0,n.
  ls = 〈grid,false〉::ls0 → 
  cur = 〈c,true〉 → 
  rs = l1@〈grid,false〉::l2@〈bar,false〉::〈c1,true〉::l3@〈grid,false〉::rs0 → 
  is_bit c = true → is_bit c1 = true → 
  only_bits_or_nulls l1 → no_marks l1 → S n = |l1| →
  table_TM (S n) (l2@〈bar,false〉::〈c1,false〉::l3) → 
  (* facciamo match *)
  (∃l4,newc,mv,l5.
   〈bar,false〉::〈c1,false〉::l3 = l4@〈bar,false〉::〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l5 ∧
   t2 = midtape ? (reverse ? l1@〈c,false〉::〈grid,false〉::ls0) 〈grid,false〉
        (l2@l4@〈bar,false〉::〈c,false〉::l1@〈comma,true〉::newc@〈comma,false〉::mv::l5@
        〈grid,false〉::rs0))
  ∨
  (* non facciamo match su nessuna tupla;
     non specifichiamo condizioni sul nastro di output, perché
     non eseguiremo altre operazioni, quindi il suo formato non ci interessa *)
  (current ? t2 = Some ? 〈grid,true〉 ∧
   ∀l4,newc,mv,l5.
   〈bar,false〉::〈c1,false〉::l3 ≠ l4@〈bar,false〉::〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l5)).  

axiom table_bit_after_bar : 
  ∀n,l1,c,l2.table_TM n (l1@〈bar,false〉::〈c,false〉::l2) → is_bit c = true.

lemma wsem_match_tuple : WRealize ? match_tuple R_match_tuple0.
#intape #k #outc #Hloop 
lapply (sem_while … sem_match_tuple_step intape k outc Hloop) [%] -Hloop
* #ta * #Hstar @(star_ind_l ??????? Hstar)
[ #tb whd in ⊢ (%→?); #Hleft
  #ls #cur #rs #Htb cases (Hleft … Htb) #Hgrid #Houtc %
  [ #_ @Houtc 
  | #c #l1 #c1 #l2 #l3 #ls0 #rs0 #n #Hls #Hcur #Hrs 
    >Hcur in Hgrid; #Hgrid >(is_grid_true … Hgrid) normalize in ⊢ (%→?);
    #Hc destruct (Hc)
  ]
| (* in the interesting case, we execute a true iteration, then we restart the
     while cycle, finally we end with a false iteration *)
  #tb #tc #td whd in ⊢ (%→?); #Htc
  #Hstar1 #IH whd in ⊢ (%→?); #Hright lapply (IH Hright) -IH whd in ⊢ (%→?); #IH
  #ls #cur #rs #Htb %
  [ (* cur can't be true because we assume at least one iteration *)
    #Hcur cases (Htc … Htb) * #Hfalse @False_ind @Hfalse @(is_grid_true … Hcur)
  | (* current and a tuple are marked *)
   #c #l1 #c1 #l2 #l3 #ls0 #rs0 #n #Hls #Hcur #Hrs #Hc #Hc1 #Hl1bitnull #Hl1marks 
   #Hl1len #Htable cases (Htc … Htb) -Htc -Htb * #_ #Htc
   (* expose the marked tuple in table *)
   cut (∃la,lb,mv,lc.l3 = la@〈comma,false〉::lb@〈comma,false〉::mv::lc ∧
         S n = |la| ∧ only_bits_or_nulls la)
   [@daemon] * #la * #lb * #mv * #lc * * #Hl3 #Hlalen #Hlabitnull
   >Hl3 in Htable; >append_cons #Htable
   >(?: l2@〈bar,false〉::〈c1,true〉::l3@〈grid,false〉::rs0
      = (l2@[〈bar,false〉])@〈c1,true〉::la@〈comma,false〉::(lb@〈comma,false〉::mv::
         lc)@〈grid,false〉::rs0) in Hrs;
   [| >associative_append normalize >Hl3
      >associative_append normalize % ] #Hrs
   cases (Htc ????????? Hl1bitnull Hl1marks ?? Hlabitnull Hl1len ? Htable Hls Hcur Hrs)
   [5: <Hl1len @Hlalen
   |4: whd in ⊢ (??%?); >Hc1 %
   |3: whd in ⊢ (??%?); >Hc %
   |-Htc *
     [ (* case 1: match successful *)
       * #Heq #Htc % %{[]} %{lb} %{mv} %{lc} destruct (Heq) %
       [%
       | cases (IH … Htc) -IH #Houtc #_ >(Houtc (refl ??)) 
         >Htc @eq_f normalize >associative_append normalize
         >associative_append normalize %
       ]     
     | (* case 2: tuples don't match, we still have other tuples to try *)
       * #Hdiff * #c2 * #l5 * #l6 * #Heqlblc #Htc
       cases (IH ??? … Htc) -IH #_ #IH 
       (* by induction hypothesis *)
       lapply (IH ? l1 c2 (l2@〈bar,false〉::〈c1,false〉::la@〈comma,false〉::l5) l6 ? rs0 n (refl ??) (refl ??) ???????)
       [ generalize in match Htable;
         >associative_append normalize 
         >associative_append normalize >Heqlblc
         >associative_append normalize //
       | @Hl1len
       | @Hl1marks
       | @Hl1bitnull
       | (*???*) @daemon
       | @Hc
       | >associative_append normalize 
         >associative_append normalize
         >associative_append %
       |-IH * 
         [ (* the while finally matches a tuple *)
           * #l7 * #newc * #mv0 * #l8 * #Hl7l8 #Houtc %
           >Heqlblc @(ex_intro ?? (〈bar,false〉::〈c1,false〉::la@〈comma,false〉::l5@l7))
           %{newc} %{mv0} %{l8} %
           [ normalize >Hl7l8 >associative_append normalize 
             >associative_append %
           | >Houtc @eq_f >associative_append normalize
             >associative_append normalize >associative_append 
             normalize >associative_append %
           ]
         | (* the while fails finding a tuple: there are no matches in the whole table *)
           * #Houtc #Hdiff1 %2 %
           [ @Houtc
           | #l50 #newc #mv0 #l51 >Heqlblc 
             @daemon
           ]
         ]
       ]
     ]
   | (* match failed and there is no next tuple: the next while cycle will just exit *)
     * * #Hdiff #Hnobars generalize in match (refl ? tc);
     cases tc in ⊢ (???% → %);
     [ #_ normalize in ⊢ (??%?→?); #Hfalse destruct (Hfalse)
     |2,3: #x #xs #_ normalize in ⊢ (??%?→?); #Hfalse destruct (Hfalse) ]
     #ls1 #cur1 #rs1 #Htc normalize in ⊢ (??%?→?); #Hcur1
     cases (IH … Htc) -IH #IH #_ %2 %
     [ destruct (Hcur1) >IH [ >Htc % | % ]
     | #l4 #newc #mv0 #l5
       (* no_bars except the first one, where the tuple does not match ⇒ 
          no match *)
        @daemon
     ]
   ]
 ]
qed.

definition R_match_tuple ≝ λt1,t2.
  ∀ls,c,l1,c1,l2,rs,n.
  is_bit c = true → is_bit c1 = true →
  only_bits_or_nulls l1 → no_marks l1 → S n = |l1| → 
  table_TM (S n) (〈bar,false〉::〈c1,false〉::l2) → 
  t1 = midtape STape (〈grid,false〉::ls) 〈c,true〉 
         (l1@〈grid,false〉::〈bar,false〉::〈c1,true〉::l2@〈grid,false〉::rs) → 
  (* facciamo match *)
  (∃l3,newc,mv,l4.
   〈bar,false〉::〈c1,false〉::l2 = l3@〈bar,false〉::〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l4 ∧
   t2 = midtape ? (reverse ? l1@〈c,false〉::〈grid,false〉::ls) 〈grid,false〉
        (l3@〈bar,false〉::〈c,false〉::l1@〈comma,true〉::newc@〈comma,false〉::mv::l4@〈grid,false〉::rs))
  ∨
  (* non facciamo match su nessuna tupla;
     non specifichiamo condizioni sul nastro di output, perché
     non eseguiremo altre operazioni, quindi il suo formato non ci interessa *)
  (current ? t2 = Some ? 〈grid,true〉 ∧
   ∀l3,newc,mv,l4.
   〈bar,false〉::〈c1,false〉::l2 ≠ l3@〈bar,false〉::〈c,false〉::l1@〈comma,false〉::newc@〈comma,false〉::mv::l4). 

(* we still haven't proved termination *)
axiom sem_match_tuple0 : Realize ? match_tuple R_match_tuple0.

lemma sem_match_tuple : Realize ? match_tuple R_match_tuple.
generalize in match sem_match_tuple0; @Realize_to_Realize
#t1 #t2 #HR #ls #c #l1 #c1 #l2 #rs #n #Hc #Hc1 #Hl1bitsnulls #Hl1marks #Hl1len #Htable #Ht1
cases (HR … Ht1) -HR #_ #HR
@(HR ??? [] … (refl ??) (refl ??) (refl ??) Hc Hc1 Hl1bitsnulls Hl1marks
          Hl1len  Htable)
qed.