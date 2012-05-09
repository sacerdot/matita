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


(* COMPARE BIT

*)

include "turing/while_machine.ma".

(* ADVANCE TO MARK (right)

   sposta la testina a destra fino a raggiungere il primo carattere marcato 
   
*)

(* 0, a ≠ mark _ ⇒ 0, R
0, a = mark _ ⇒ 1, N *)

definition atm_states ≝ initN 3.

definition atmr_step ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha atm_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈1, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈1,None ?〉
     | false ⇒ 〈2,Some ? 〈a',R〉〉 ]])
  O (λx.notb (x == 0)).

definition Ratmr_step_true ≝ 
  λalpha,test,t1,t2.
   ∃ls,a,rs.
   t1 = midtape alpha ls a rs ∧ test a = false ∧ 
   t2 = mk_tape alpha (a::ls) (option_hd ? rs) (tail ? rs).
   
definition Ratmr_step_false ≝ 
  λalpha,test,t1,t2.
    t1 = t2 ∧
    (current alpha t1 = None ? ∨
     (∃a.current ? t1 = Some ? a ∧ test a = true)).
     
lemma atmr_q0_q1 :
  ∀alpha,test,ls,a0,rs. test a0 = true → 
  step alpha (atmr_step alpha test)
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) 1
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest normalize >Htest %
qed.
     
lemma atmr_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (atmr_step alpha test)
    (mk_config ?? 0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) 2
    (mk_tape … (a0::ls) (option_hd ? rs) (tail ? rs)).
#alpha #test #ls #a0 #ts #Htest normalize >Htest cases ts //
qed.

lemma sem_atmr_step :
  ∀alpha,test.
  accRealize alpha (atmr_step alpha test) 
    2 (Ratmr_step_true alpha test) (Ratmr_step_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? 1 (niltape ?))) %
  [ % // #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (leftof ? a al)))
  % [ % // #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? 1 (rightof ? a al)))
  % [ % // #Hfalse destruct | #_ % // % % ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? 1 ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >atmr_q0_q1 //
        | #Hfalse destruct ]
      | #_ % // %2 @(ex_intro ?? c) % // ]
    ]
  | @(ex_intro ?? (mk_config ?? 2 (mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs))))
    % 
    [ %
      [ whd in ⊢ (??%?); >atmr_q0_q2 //
      | #_ @(ex_intro ?? ls) @(ex_intro ?? c) @(ex_intro ?? rs)
        % // % //
      ]
    | #Hfalse @False_ind @(absurd ?? Hfalse) %
    ]
  ]
]
qed.

(*
definition R_adv_to_mark_r ≝ λalpha,test,t1,t2.
  ∀ls,c,rs.
  t1 = mk_tape alpha ls c rs  → 
  (c = None ? ∧ t2 = t1) ∨  
  (∃c'.c = Some ? c' ∧
    ((test c' = true ∧ t2 = t1) ∨
     (test c' = false ∧
       (((∀x.memb ? x rs = true → test x = false) ∧
         t2 = mk_tape ? (reverse ? rs@c'::ls) (None ?) []) ∨
        (∃rs1,b,rs2.rs = rs1@b::rs2 ∧
         test b = true ∧ (∀x.memb ? x rs1 = true → test x = false) ∧
         t2 = midtape ? (reverse ? rs1@c'::rs) b rs2))))).
     
definition adv_to_mark_r ≝ 
  λalpha,test.whileTM alpha (atmr_step alpha test) 2.

lemma wsem_adv_to_mark_r :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atmr_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 #ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
    #Hfalse destruct (Hfalse)
  | * #a * #Ha #Htest #ls #c #rs cases c
    [ #Htapea' % % // >Htapea %
    | #c' #Htapea' %2 @(ex_intro ?? c') % //
      cases (true_or_false (test c')) #Htestc
      [ % % // >Htapea %
      | %2 % // generalize in match Htapea'; -Htapea'
        cases rs
        [ #Htapea' % %
          [ normalize #x #Hfalse destruct (Hfalse)
          | <Htapea >Htapea' % 
    
    
   #H2 %
    >H2 in Ha; whd in ⊢ (??%? → ?); #Heq destruct (Heq) % // <Htapea //
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH
  #ls #c #rs #Htapea
  cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest #Htapeb
  >Htapea' in Htapea; #Htapea destruct (Htapea) %2 % //
  generalize in match Htapeb; -Htapeb
  generalize in match Htapea'; -Htapea'
  cases rs
  [ #Htapea #Htapeb % %
    [ #x0 normalize #Hfalse destruct (Hfalse)
    | normalize in Htapeb; cases (IH
  
  
   [//]  
   cases (true_or_false (test c))
  [ #Htestc %
  
  
  [ #Htapea %2 % [ %2 // ]
    #rs #Htapea %2
  

   *
  [ #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #_
    cases (IH … Htapeb)
    [ * #_ #Houtc >Houtc >Htapeb %
    | * #Hfalse >Hfalse in Htestb; #Htestb destruct (Htestb) ]
  | #r1 #rs1 #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #Hmemb
    cases (IH … Htapeb)
    [ * #Hfalse >(Hmemb …) in Hfalse;
      [ #Hft destruct (Hft)
      | @memb_hd ]
    | * #Htestr1 #H1 >reverse_cons >associative_append
      @H1 // #x #Hx @Hmemb @memb_cons //
    ]
  ]
qed. *)

definition R_adv_to_mark_r ≝ λalpha,test,t1,t2.
  ∀ls,c,rs.
  (t1 = midtape alpha ls c rs  → 
  ((test c = true ∧ t2 = t1) ∨
   (test c = false ∧
    ∀rs1,b,rs2. rs = rs1@b::rs2 → 
     test b = true → (∀x.memb ? x rs1 = true → test x = false) → 
     t2 = midtape ? (reverse ? rs1@c::ls) b rs2))).
     
definition adv_to_mark_r ≝ 
  λalpha,test.whileTM alpha (atmr_step alpha test) 2.

lemma wsem_adv_to_mark_r :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atmr_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 #ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
    #Hfalse destruct (Hfalse)
  | * #a * #Ha #Htest #ls #c #rs #H2 %
    >H2 in Ha; whd in ⊢ (??%? → ?); #Heq destruct (Heq) % //
    <Htapea //
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH
  #ls #c #rs #Htapea %2
  cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest #Htapeb
  
  >Htapea' in Htapea; #Htapea destruct (Htapea) % // *
  [ #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #_
    cases (IH … Htapeb)
    [ * #_ #Houtc >Houtc >Htapeb %
    | * #Hfalse >Hfalse in Htestb; #Htestb destruct (Htestb) ]
  | #r1 #rs1 #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #Hmemb
    cases (IH … Htapeb)
    [ * #Hfalse >(Hmemb …) in Hfalse;
      [ #Hft destruct (Hft)
      | @memb_hd ]
    | * #Htestr1 #H1 >reverse_cons >associative_append
      @H1 // #x #Hx @Hmemb @memb_cons //
    ]
  ]
qed.

lemma terminate_adv_to_mark_r :
  ∀alpha,test.
  ∀t.Terminate alpha (adv_to_mark_r alpha test) t.
#alpha #test #t
@(terminate_while … (sem_atmr_step alpha test))
  [ %
  | cases t
    [ % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    |2,3: #a0 #al0 % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    | #ls #c #rs generalize in match c; -c generalize in match ls; -ls
      elim rs
      [#ls #c % #t1 * #ls0 * #c0 * #rs0 * *
       #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1; 
       % #t2 * #ls1 * #c1 * #rs1 * * >Ht1
       normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
      | #r0 #rs0 #IH #ls #c % #t1 * #ls0 * #c0 * #rs0 * *
        #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1;
        >Ht1 @IH
      ]
    ]
  ]
qed.

lemma sem_adv_to_mark_r :
  ∀alpha,test.
  Realize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
/2/
qed.

(* NO OPERATION

  t1 = t2
  *)
  
definition nop_states ≝ initN 1.

definition nop ≝ 
  λalpha:FinSet.mk_TM alpha nop_states
  (λp.let 〈q,a〉 ≝ p in 〈q,None ?〉)
  O (λ_.true).
  
definition R_nop ≝ λalpha.λt1,t2:tape alpha.t2 = t1.

lemma sem_nop :
  ∀alpha.Realize alpha (nop alpha) (R_nop alpha).
#alpha #intape @(ex_intro ?? 1) @ex_intro [| % normalize % ]
qed.

(*
   q0 _ → q1, R
   q1 〈a,false〉 → qF, 〈a,true〉, N
   q1 〈a,true〉 → qF, _ , N
   qF _ → None ?
 *)
 
definition mark_states ≝ initN 3.

definition mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) mark_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈2,None ?〉
    | Some a' ⇒ match q with
      [ O ⇒ 〈1,Some ? 〈a',R〉〉
      | S q ⇒ match q with
        [ O ⇒ let 〈a'',b〉 ≝ a' in
              〈2,Some ? 〈〈a'',true〉,N〉〉
        | S _ ⇒ 〈2,None ?〉 ] ] ])
  O (λq.q == 2).
  
definition R_mark ≝ λalpha,t1,t2.
  ∀ls,c,d,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls c (〈d,b〉::rs) → 
  t2 = midtape ? (c::ls) 〈d,true〉 rs.
  
(*lemma mark_q0_q1 : 
  ∀alpha,ls,c,rs.
  step alpha (mark alpha)
    (mk_config ?? 0 (midtape … ls c rs)) =
  mk_config alpha (states ? (mark alpha)) 1
    (midtape … (ls a0 rs).*)
  
lemma sem_mark :
  ∀alpha.Realize ? (mark alpha) (R_mark alpha).
#alpha #intape @(ex_intro ?? 3) cases intape
[ @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
|#a #al @ex_intro
  [| % [ % | #ls #c #d #b #rs #Hfalse destruct ] ]
| #ls #c *
  [ @ex_intro [| % [ % | #ls0 #c0 #d0 #b0 #rs0 #Hfalse destruct ] ]
  | * #d #b #rs @ex_intro
    [| % [ % | #ls0 #c0 #d0 #b0 #rs0 #H1 destruct (H1) % ] ] ] ]
qed.

include "turing/if_machine.ma".

(* TEST CHAR 

   stato finale diverso a seconda che il carattere 
   corrente soddisfi un test booleano oppure no  
   
   q1 = true or no current char
   q2 = false
*)

definition tc_states ≝ initN 3.

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

axiom myalpha : FinSet.
axiom is_bar : FinProd … myalpha FinBool → bool.
axiom is_grid : FinProd … myalpha FinBool → bool.
definition bar_or_grid ≝ λc.is_bar c ∨ is_grid c.
axiom bar : FinProd … myalpha FinBool.
axiom grid : FinProd … myalpha FinBool.

definition mark_next_tuple ≝ 
  seq ? (adv_to_mark_r ? bar_or_grid)
     (ifTM ? (test_char ? is_bar)
       (mark ?) (nop ?) 1).

definition R_mark_next_tuple ≝ 
  λt1,t2.
    ∀ls,c,rs1,rs2.
    (* c non può essere un separatore ... speriamo *)
    t1 = midtape ? ls c (rs1@grid::rs2) → 
    memb ? grid rs1 = false → bar_or_grid c = false → 
    (∃rs3,rs4,d,b.rs1 = rs3 @ bar :: rs4 ∧
      memb ? bar rs3 = false ∧ 
      Some ? 〈d,b〉 = option_hd ? (rs4@grid::rs2) ∧
      t2 = midtape ? (bar::reverse ? rs3@c::ls) 〈d,true〉 (tail ? (rs4@grid::rs2)))
    ∨
    (memb ? bar rs1 = false ∧ 
     t2 = midtape ? (reverse ? rs1@c::ls) grid rs2).
     
axiom tech_split :
  ∀A:DeqSet.∀f,l.
   (∀x.memb A x l = true → f x = false) ∨
   (∃l1,c,l2.f c = true ∧ l = l1@c::l2 ∧ ∀x.memb ? x l1 = true → f c = false).
(*#A #f #l elim l
[ % #x normalize #Hfalse *)
     
theorem sem_mark_next_tuple :
  Realize ? mark_next_tuple R_mark_next_tuple.
#intape 
lapply (sem_seq ? (adv_to_mark_r ? bar_or_grid)
         (ifTM ? (test_char ? is_bar) (mark ?) (nop ?) 1) ????)
[@sem_if //
| //
|||#Hif cases (Hif intape) -Hif
   #j * #outc * #Hloop * #ta * #Hleft #Hright
   @(ex_intro ?? j) @ex_intro [|% [@Hloop] ]
   -Hloop
   #ls #c #rs1 #rs2 #Hrs #Hrs1 #Hc
   cases (Hleft … Hrs)
   [ * #Hfalse >Hfalse in Hc; #Htf destruct (Htf)
   | * #_ #Hta cases (tech_split ? is_bar rs1)
     [ #H1 lapply (Hta rs1 grid rs2 (refl ??) ? ?)
       [ (* Hrs1, H1 *) @daemon
       | (* bar_or_grid grid = true *) @daemon
       | -Hta #Hta cases Hright
         [ * #tb * whd in ⊢ (%→?); #Hcurrent
           @False_ind cases(Hcurrent grid ?)
           [ #Hfalse (* grid is not a bar *) @daemon
           | >Hta % ]
         | * #tb * whd in ⊢ (%→?); #Hcurrent
           cases (Hcurrent grid ?)
           [  #_ #Htb whd in ⊢ (%→?); #Houtc
             %2 %
             [ (* H1 *) @daemon
             | >Houtc >Htb >Hta % ]
           | >Hta % ]
         ]
       ]
    | * #rs3 * #c0 * #rs4 * * #Hc0 #Hsplit #Hrs3
      % @(ex_intro ?? rs3) @(ex_intro ?? rs4)
     lapply (Hta rs3 c0 (rs4@grid::rs2) ???)
     [ #x #Hrs3' (* Hrs1, Hrs3, Hsplit *) @daemon
     | (* bar → bar_or_grid *) @daemon
     | >Hsplit >associative_append % ] -Hta #Hta
       cases Hright
       [ * #tb * whd in ⊢ (%→?); #Hta'
         whd in ⊢ (%→?); #Htb
         cases (Hta' c0 ?)
         [ #_ #Htb' >Htb' in Htb; #Htb
           generalize in match Hsplit; -Hsplit
           cases rs4 in Hta;
           [ >(eq_pair_fst_snd … grid)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst grid)) @(ex_intro ?? (\snd grid))
               % [ % [ % [ (* Hsplit *) @daemon |(*Hrs3*) @daemon ] | % ] | % ] 
                     | (* Hc0 *) @daemon ]
           | #r5 #rs5 >(eq_pair_fst_snd … r5)
             #Hta #Hsplit >(Htb … Hta)
             >(?:c0 = bar)
             [ @(ex_intro ?? (\fst r5)) @(ex_intro ?? (\snd r5))
               % [ % [ % [ (* Hc0, Hsplit *) @daemon | (*Hrs3*) @daemon ] | % ]
                     | % ] | (* Hc0 *) @daemon ] ] | >Hta % ]
             | * #tb * whd in ⊢ (%→?); #Hta'
               whd in ⊢ (%→?); #Htb
               cases (Hta' c0 ?)
               [ #Hfalse @False_ind >Hfalse in Hc0;
                 #Hc0 destruct (Hc0)
               | >Hta % ]
]]]]
qed.