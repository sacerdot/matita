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

include "turing/if_machine.ma".
include "turing/basic_machines.ma".
include "turing/universal/alphabet.ma".

(* ADVANCE TO MARK (right)

   sposta la testina a destra fino a raggiungere il primo carattere marcato 
   
*)

(* 0, a ≠ mark _ ⇒ 0, R
0, a = mark _ ⇒ 1, N *)

definition atm_states ≝ initN 3.

definition atm0 : atm_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition atm1 : atm_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition atm2 : atm_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition atmr_step ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha atm_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈atm1, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈atm1,None ?〉
     | false ⇒ 〈atm2,Some ? 〈a',R〉〉 ]])
  atm0 (λx.notb (x == atm0)).

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
    (mk_config ?? atm0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) atm1
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?);
whd in match (trans … 〈?,?〉); >Htest %
qed.
     
lemma atmr_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (atmr_step alpha test)
    (mk_config ?? atm0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atmr_step alpha test)) atm2
    (mk_tape … (a0::ls) (option_hd ? rs) (tail ? rs)).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?);
whd in match (trans … 〈?,?〉); >Htest cases ts //
qed.

lemma sem_atmr_step :
  ∀alpha,test.
  accRealize alpha (atmr_step alpha test) 
    atm2 (Ratmr_step_true alpha test) (Ratmr_step_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? atm1 (niltape ?))) %
  [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? atm1 (leftof ? a al)))
  % [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? atm1 (rightof ? a al)))
  % [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? atm1 ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >atmr_q0_q1 //
        | whd in ⊢ ((??%%)→?); #Hfalse destruct ]
      | #_ % // %2 @(ex_intro ?? c) % // ]
    ]
  | @(ex_intro ?? (mk_config ?? atm2 (mk_tape ? (c::ls) (option_hd ? rs) (tail ? rs))))
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

lemma dec_test: ∀alpha,rs,test. 
 decidable (∀c.memb alpha c rs = true → test c = false).
#alpha #rs #test elim rs 
  [%1 #n normalize #H destruct
  |#a #tl cases (true_or_false (test a)) #Ha 
    [#_ %2 % #Hall @(absurd ?? not_eq_true_false) <Ha 
     @Hall @memb_hd 
    |* [#Hall %1 #c #memc cases (orb_true_l … memc) 
         [#eqca >(\P eqca) @Ha |@Hall]
    |#Hnall %2 @(not_to_not … Hnall) #Hall #c #memc @Hall @memb_cons //
    ]
  qed.

definition R_adv_to_mark_r ≝ λalpha,test,t1,t2.
  (current ? t1 = None ? → t1 = t2) ∧
  ∀ls,c,rs.
  (t1 = midtape alpha ls c rs  → 
  ((test c = true ∧ t2 = t1) ∨
   (test c = false ∧
    (∀rs1,b,rs2. rs = rs1@b::rs2 → 
     test b = true → (∀x.memb ? x rs1 = true → test x = false) → 
     t2 = midtape ? (reverse ? rs1@c::ls) b rs2) ∧
     ((∀x.memb ? x rs = true → test x = false) → 
      ∀a,l.reverse ? (c::rs) = a::l → 
      t2 = rightof alpha a (l@ls))))).
     
definition adv_to_mark_r ≝ 
  λalpha,test.whileTM alpha (atmr_step alpha test) atm2.

lemma wsem_adv_to_mark_r :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_r alpha test) (R_adv_to_mark_r alpha test).
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atmr_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 %
    [#_ @Htapea 
    |#ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
     #Hfalse destruct (Hfalse)
    ]
  | * #a * #Ha #Htest %
    [ >Ha #H destruct (H);
    | #ls #c #rs #H2 %
     >H2 in Ha; whd in ⊢ (??%? → ?); #Heq destruct (Heq) % //
     <Htapea //
    ]
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH %
  [cases Hleft #ls * #a * #rs * * #Htapea #_ #_ >Htapea
   whd in ⊢((??%?)→?); #H destruct (H);
  |#ls #c #rs #Htapea %2
   cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest #Htapeb
   >Htapea' in Htapea; #Htapea destruct (Htapea) % [ % // ]
   [*
    [ #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #_
     cases (proj2 ?? IH … Htapeb)
      [ * #_ #Houtc >Houtc >Htapeb %
      | * * >Htestb #Hfalse destruct (Hfalse) ]
    | #r1 #rs1 #b #rs2 #Hrs >Hrs in Htapeb; #Htapeb #Htestb #Hmemb
     cases (proj2 ?? IH … Htapeb)
      [ * #Hfalse >(Hmemb …) in Hfalse;
        [ #Hft destruct (Hft)
        | @memb_hd ]
      | * * #Htestr1 #H1 #_ >reverse_cons >associative_append
       @H1 // #x #Hx @Hmemb @memb_cons //
      ]
    ]
   |cases rs in Htapeb; normalize in ⊢ (%→?);
    [#Htapeb #_ #a0 #l whd in ⊢ ((??%?)→?); #Hrev destruct (Hrev) 
     >Htapeb in IH; #IH cases (proj1 ?? IH … (refl …)) //
    |#r1 #rs1 #Htapeb #Hmemb
     cases (proj2 ?? IH … Htapeb) [ * >Hmemb [ #Hfalse destruct(Hfalse) ] @memb_hd ]
     * #_ #H1 #a #l <(reverse_reverse … l) cases (reverse … l)
      [#H cut (c::r1::rs1 = [a])
        [<(reverse_reverse  … (c::r1::rs1)) >H //]
       #Hrev destruct (Hrev)
      |#a1 #l2 >reverse_cons >reverse_cons >reverse_cons 
       #Hrev cut ([c] = [a1])
        [@(append_l2_injective_r ?? (a::reverse … l2) … Hrev) //]
       #Ha <Ha >associative_append @H1
        [#x #membx @Hmemb @memb_cons @membx
        |<(append_l1_injective_r ?? (a::reverse … l2) … Hrev) //
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

(* MARK machine

   marks the current character 
 *)
 
definition mark_states ≝ initN 2.

definition ms0 : mark_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition ms1 : mark_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) mark_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈ms1,None ?〉
    | Some a' ⇒ match (pi1 … q) with
      [ O ⇒ let 〈a'',b〉 ≝ a' in 〈ms1,Some ? 〈〈a'',true〉,N〉〉
      | S q ⇒ 〈ms1,None ?〉 ] ])
  ms0 (λq.q == ms1).
  
definition R_mark ≝ λalpha,t1,t2.
  (∀ls,c,b,rs.
     t1 = midtape (FinProd … alpha FinBool) ls 〈c,b〉 rs → 
     t2 = midtape ? ls 〈c,true〉 rs) ∧
  (current ? t1 = None ? → t2 = t1).
    
lemma sem_mark :
  ∀alpha.Realize ? (mark alpha) (R_mark alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | % [#ls #c #b #rs #Hfalse destruct | // ]]]
|#a #al @ex_intro
  [| % [ % | % [#ls #c #b #rs #Hfalse destruct | // ]]]
|#a #al @ex_intro
  [| % [ % | % [#ls #c #b #rs #Hfalse destruct ] // ]]
| #ls * #c #b #rs
  @ex_intro [| % [ % | % 
  [#ls0 #c0 #b0 #rs0 #H1 destruct (H1) % 
  | whd in ⊢ ((??%?)→?); #H1 destruct (H1)]]]
qed.


(* MOVE RIGHT AND MARK machine

   marks the first character on the right
   
   (could be rewritten using (mark; move_right))
 *)
 
definition mrm_states ≝ initN 3.

definition mrm0 : mrm_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition mrm1 : mrm_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition mrm2 : mrm_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition move_right_and_mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) mrm_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈mrm2,None ?〉
    | Some a' ⇒ match pi1 … q with
      [ O ⇒ 〈mrm1,Some ? 〈a',R〉〉
      | S q ⇒ match q with
        [ O ⇒ let 〈a'',b〉 ≝ a' in
              〈mrm2,Some ? 〈〈a'',true〉,N〉〉
        | S _ ⇒ 〈mrm2,None ?〉 ] ] ])
  mrm0 (λq.q == mrm2).
  
definition R_move_right_and_mark ≝ λalpha,t1,t2.
  ∀ls,c,d,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls c (〈d,b〉::rs) → 
  t2 = midtape ? (c::ls) 〈d,true〉 rs.
    
lemma sem_move_right_and_mark :
  ∀alpha.Realize ? (move_right_and_mark alpha) (R_move_right_and_mark alpha).
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

(* CLEAR MARK machine

   clears the mark in the current character 
 *)
 
definition clear_mark_states ≝ initN 3.

definition clear0 : clear_mark_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition clear1 : clear_mark_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition claer2 : clear_mark_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

definition clear_mark ≝ 
  λalpha:FinSet.mk_TM (FinProd … alpha FinBool) clear_mark_states
  (λp.let 〈q,a〉 ≝ p in
    match a with
    [ None ⇒ 〈clear1,None ?〉
    | Some a' ⇒ match pi1 … q with
      [ O ⇒ let 〈a'',b〉 ≝ a' in 〈clear1,Some ? 〈〈a'',false〉,N〉〉
      | S q ⇒ 〈clear1,None ?〉 ] ])
  clear0 (λq.q == clear1).
  
definition R_clear_mark ≝ λalpha,t1,t2.
  (current ? t1 = None ? → t1 = t2) ∧
  ∀ls,c,b,rs.
  t1 = midtape (FinProd … alpha FinBool) ls 〈c,b〉 rs → 
  t2 = midtape ? ls 〈c,false〉 rs.
    
lemma sem_clear_mark :
  ∀alpha.Realize ? (clear_mark alpha) (R_clear_mark alpha).
#alpha #intape @(ex_intro ?? 2) cases intape
[ @ex_intro
  [| % [ % | % [#_ %|#ls #c #b #rs #Hfalse destruct ]]]
|#a #al @ex_intro
  [| % [ % | % [#_ %|#ls #c #b #rs #Hfalse destruct ]]]
|#a #al @ex_intro
  [| % [ % | % [#_ %|#ls #c #b #rs #Hfalse destruct ]]]
| #ls * #c #b #rs
  @ex_intro [| % [ % | % 
  [whd in ⊢ (??%?→?); #H destruct| #ls0 #c0 #b0 #rs0 #H1 destruct (H1) % ]]]]
qed.

(* ADVANCE MARK RIGHT machine

   clears mark on current char,
   moves right, and marks new current char
   
*)

definition adv_mark_r ≝ 
  λalpha:FinSet.
    clear_mark alpha · move_r ? · mark alpha.
      
definition R_adv_mark_r ≝ λalpha,t1,t2.
  (∀ls,c.
    (∀d,b,rs.
     t1 = midtape (FinProd … alpha FinBool) ls 〈c,true〉 (〈d,b〉::rs) → 
     t2 = midtape ? (〈c,false〉::ls) 〈d,true〉 rs) ∧
    (t1 = midtape (FinProd … alpha FinBool) ls 〈c,true〉 [ ] → 
     t2 = rightof ? 〈c,false〉 ls)) ∧
  (current ? t1 = None ? → t1 = t2).
  
lemma sem_adv_mark_r : 
  ∀alpha.Realize ? (adv_mark_r alpha) (R_adv_mark_r alpha).
#alpha
@(sem_seq_app … (sem_clear_mark …) 
         (sem_seq ????? (sem_move_r ?) (sem_mark alpha)) …)
#intape #outtape whd in ⊢ (%→?); * #ta * 
whd in ⊢ (%→?); #Hs1 whd in ⊢ (%→?); * #tb * #Hs2 whd in ⊢ (%→?); #Hs3 %
  [#ls #c % 
    [#d #b #rs #Hintape @(proj1 … Hs3 ?? b ?)
     @(proj2 … Hs2 ls 〈c,false〉 (〈d,b〉::rs))
     @(proj2 ?? Hs1 … Hintape)
    |#Hintape lapply (proj2 ?? Hs1 … Hintape) #Hta lapply (proj2 … Hs2 … Hta) 
     whd in ⊢ ((???%)→?); #Htb <Htb @(proj2 … Hs3) >Htb //
    ]
  |#Hcur lapply(proj1 ?? Hs1 … Hcur) #Hta >Hta >Hta in Hcur; #Hcur
   lapply (proj1 ?? Hs2 … Hcur) #Htb >Htb >Htb in Hcur; #Hcur
   @sym_eq @(proj2 ?? Hs3) @Hcur
  ]
qed.

(* ADVANCE TO MARK (left)

axiomatized

*)
definition atml_step ≝ 
  λalpha:FinSet.λtest:alpha→bool.
  mk_TM alpha atm_states
  (λp.let 〈q,a〉 ≝ p in
   match a with
   [ None ⇒ 〈atm1, None ?〉
   | Some a' ⇒ 
     match test a' with
     [ true ⇒ 〈atm1,None ?〉
     | false ⇒ 〈atm2,Some ? 〈a',L〉〉 ]])
  atm0 (λx.notb (x == atm0)).

definition Ratml_step_true ≝ 
  λalpha,test,t1,t2.
   ∃ls,a,rs.
   t1 = midtape alpha ls a rs ∧ test a = false ∧ 
   t2 = mk_tape alpha (tail ? ls) (option_hd ? ls) (a :: rs).
   
definition Ratml_step_false ≝ 
  λalpha,test,t1,t2.
    t1 = t2 ∧
    (current alpha t1 = None ? ∨
     (∃a.current ? t1 = Some ? a ∧ test a = true)).
     
lemma atml_q0_q1 :
  ∀alpha,test,ls,a0,rs. test a0 = true → 
  step alpha (atml_step alpha test)
    (mk_config ?? atm0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atml_step alpha test)) atm1
    (midtape … ls a0 rs).
#alpha #test #ls #a0 #ts #Htest whd in ⊢ (??%?);
whd in match (trans … 〈?,?〉); >Htest %
qed.
     
lemma atml_q0_q2 :
  ∀alpha,test,ls,a0,rs. test a0 = false → 
  step alpha (atml_step alpha test)
    (mk_config ?? atm0 (midtape … ls a0 rs)) =
  mk_config alpha (states ? (atml_step alpha test)) atm2
    (mk_tape … (tail ? ls) (option_hd ? ls) (a0 :: rs)).
#alpha #test #ls #a0 #rs #Htest whd in ⊢ (??%?);
whd in match (trans … 〈?,?〉); >Htest cases ls //
qed.

lemma sem_atml_step :
  ∀alpha,test.
  accRealize alpha (atml_step alpha test) 
    atm2 (Ratml_step_true alpha test) (Ratml_step_false alpha test).
#alpha #test *
[ @(ex_intro ?? 2)
  @(ex_intro ?? (mk_config ?? atm1 (niltape ?))) %
  [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? atm1 (leftof ? a al)))
  % [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #a #al @(ex_intro ?? 2) @(ex_intro ?? (mk_config ?? atm1 (rightof ? a al)))
  % [ % // whd in ⊢ ((??%%)→?); #Hfalse destruct | #_ % // % % ]
| #ls #c #rs @(ex_intro ?? 2)
  cases (true_or_false (test c)) #Htest
  [ @(ex_intro ?? (mk_config ?? atm1 ?))
    [| % 
      [ % 
        [ whd in ⊢ (??%?); >atml_q0_q1 //
        | whd in ⊢ ((??%%)→?); #Hfalse destruct ]
      | #_ % // %2 @(ex_intro ?? c) % // ]
    ]
  | @(ex_intro ?? (mk_config ?? atm2 (mk_tape ? (tail ? ls) (option_hd ? ls) (c::rs))))
    % 
    [ %
      [ whd in ⊢ (??%?); >atml_q0_q2 //
      | #_ @(ex_intro ?? ls) @(ex_intro ?? c) @(ex_intro ?? rs)
        % // % //
      ]
    | #Hfalse @False_ind @(absurd ?? Hfalse) %
    ]
  ]
]
qed.

definition R_adv_to_mark_l ≝ λalpha,test,t1,t2.
  (current ? t1 = None ? → t1 = t2) ∧
  ∀ls,c,rs.
  (t1 = midtape alpha ls c rs  → 
  ((test c = true → t2 = t1) ∧
   (test c = false →
    (∀ls1,b,ls2. ls = ls1@b::ls2 → 
     test b = true → (∀x.memb ? x ls1 = true → test x = false) → 
     t2 = midtape ? ls2 b (reverse ? ls1@c::rs)) ∧     
    ((∀x.memb ? x ls = true → test x = false) →
      ∀a,l. reverse ? (c::ls) = a::l → t2 = leftof ? a (l@rs))
     ))).

definition adv_to_mark_l ≝ 
  λalpha,test.whileTM alpha (atml_step alpha test) atm2.

lemma wsem_adv_to_mark_l :
  ∀alpha,test.
  WRealize alpha (adv_to_mark_l alpha test) (R_adv_to_mark_l alpha test).
#alpha #test #t #i #outc #Hloop
lapply (sem_while … (sem_atml_step alpha test) t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea * #Htapea *
  [ #H1 %
    [#_ @Htapea
    |#ls #c #rs #H2 >H2 in H1; whd in ⊢ (??%? → ?);
     #Hfalse destruct (Hfalse)
    ]
  | * #a * #Ha #Htest %
    [>Ha #H destruct (H);
    |#ls #c #rs #H2 %
      [#Hc <Htapea //
      |#Hc @False_ind >H2 in Ha; whd in ⊢ ((??%?)→?); 
       #H destruct (H) /2/
      ]
    ]
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #HRfalse
  lapply (IH HRfalse) -IH #IH %
  [cases Hleft #ls0 * #a0 * #rs0 * * #Htapea #_ #_ >Htapea
   whd in ⊢ ((??%?)→?); #H destruct (H)
  |#ls #c #rs #Htapea %
    [#Hc cases Hleft #ls0 * #a0 * #rs0 * * #Htapea' #Htest @False_ind
     >Htapea' in Htapea; #H destruct /2/
    |cases Hleft #ls0 * #a * #rs0 *
     * #Htapea1 >Htapea in Htapea1; #H destruct (H) #_ #Htapeb
     #Hc %
      [*
        [#b #ls2 #Hls >Hls in Htapeb; #Htapeb #Htestb #_
         cases (proj2 ?? IH … Htapeb) #H1 #_ >H1 // >Htapeb %
        |#l1 #ls1 #b #ls2 #Hls >Hls in Htapeb; #Htapeb #Htestb #Hmemb 
         cases (proj2 ?? IH … Htapeb) #_ #H1 >reverse_cons >associative_append
         @(proj1 ?? (H1 ?) … (refl …) Htestb …)
          [@Hmemb @memb_hd
          |#x #memx @Hmemb @memb_cons @memx
          ]
        ]
      |cases ls0 in Htapeb; normalize in ⊢ (%→?);
        [#Htapeb #Htest #a0 #l whd in ⊢ ((??%?)→?); #Hrev destruct (Hrev) 
         >Htapeb in IH; #IH cases (proj1 ?? IH … (refl …)) //
        |#l1 #ls1 #Htapeb
         cases (proj2 ?? IH … Htapeb) #_ #H1 #Htest #a0 #l
         <(reverse_reverse … l) cases (reverse … l)
          [#H cut (a::l1::ls1 = [a0])
            [<(reverse_reverse  … (a::l1::ls1)) >H //]
           #Hrev destruct (Hrev)
          |#a1 #l2 >reverse_cons >reverse_cons >reverse_cons 
           #Hrev cut ([a] = [a1])
            [@(append_l2_injective_r ?? (a0::reverse … l2) … Hrev) //]
           #Ha <Ha >associative_append @(proj2 ?? (H1 ?))
            [@Htest @memb_hd
            |#x #membx @Htest @memb_cons @membx
            |<(append_l1_injective_r ?? (a0::reverse … l2) … Hrev) //
            ]
          ]
        ]
      ]
    ]
  ]
qed.

lemma terminate_adv_to_mark_l :
  ∀alpha,test.
  ∀t.Terminate alpha (adv_to_mark_l alpha test) t.
#alpha #test #t
@(terminate_while … (sem_atml_step alpha test))
  [ %
  | cases t
    [ % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    |2,3: #a0 #al0 % #t1 * #ls0 * #c0 * #rs0 * * #Hfalse destruct (Hfalse) 
    | #ls elim ls 
      [#c #rs % #t1 * #ls0 * #c0 * #rs0 * *
       #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1; 
       % #t2 * #ls1 * #c1 * #rs1 * * >Ht1
       normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
      | #rs0 #r0 #IH #ls #c % #t1 * #ls0 * #c0 * #rs0 * *
        #H1 destruct (H1) #Hc0 #Ht1 normalize in Ht1;
        >Ht1 @IH
      ]
    ]
  ]
qed.

lemma sem_adv_to_mark_l :
  ∀alpha,test.
  Realize alpha (adv_to_mark_l alpha test) (R_adv_to_mark_l alpha test).
/2/
qed.

(*
   ADVANCE BOTH MARKS machine
   
   l1 does not contain marks ⇒
   

   input:
   l0 x* a l1 x0* a0 l2
              ^
   
   output:
   l0 x a* l1 x0 a0* l2
        ^
*)

definition adv_both_marks ≝ λalpha.
  adv_mark_r alpha · move_l ? ·
    adv_to_mark_l (FinProd alpha FinBool) (is_marked alpha) · 
      adv_mark_r alpha.

definition R_adv_both_marks ≝ 
  λalpha,t1,t2.
    ∀l0,x,a,l1,x0. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    (∀l1',a0,l2. t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2) → 
     reverse ? (〈x0,false〉::l1) = 〈a,false〉::l1' →
     t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (l1'@〈a0,true〉::l2)) ∧
     (t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 [ ] → 
     t2 = rightof ? 〈x0,false〉 (l1@〈a,false〉::〈x,true〉::l0)).

lemma sem_adv_both_marks :
  ∀alpha.Realize ? (adv_both_marks alpha) (R_adv_both_marks alpha).    
#alpha 
@(sem_seq_app … (sem_adv_mark_r …) 
   (sem_seq ????? (sem_move_l …)
      (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?)) 
        (sem_adv_mark_r alpha))) …)
#intape #outtape * #tapea * #Hta * #tb * #Htb * #tc * #Htc #Hout 
#l0 #x #a #l1 #x0 #Hmarks %
  [#l1' #a0 #l2 #Hintape #Hrev @(proj1 ?? (proj1 ?? Hout … ) ? false) -Hout
   lapply (proj1 … (proj1 … Hta …) … Hintape) #Htapea
   lapply (proj2 … Htb  … Htapea) -Htb
   whd in match (mk_tape ????) ; #Htapeb 
   lapply (proj1 ?? (proj2 ?? (proj2 ?? Htc … Htapeb) (refl …))) -Htc #Htc
   change with ((?::?)@?) in match (cons ???); <Hrev >reverse_cons
   >associative_append @Htc [%|%|@Hmarks] 
  |#Hintape lapply (proj2 ?? (proj1 ?? Hta … ) … Hintape) -Hta #Hta
   lapply (proj1 … Htb) >Hta -Htb #Htb lapply (Htb (refl …)) -Htb #Htb 
   lapply (proj1 ?? Htc) <Htb -Htc #Htc lapply (Htc (refl …)) -Htc #Htc
   @sym_eq >Htc @(proj2 ?? Hout …) <Htc % 
  ]
qed.

(*
definition R_adv_both_marks ≝ 
  λalpha,t1,t2.
    ∀l0,x,a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    (t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2) → 
     t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (reverse ? l1@〈x0,false〉::〈a0,true〉::l2)) ∧
     (t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 [] → 
     t2 = rightof ? 〈x0,false〉 (l1@〈a,false〉::〈x,true〉::l0)).

lemma sem_adv_both_marks :
  ∀alpha.Realize ? (adv_both_marks alpha) (R_adv_both_marks alpha).    
#alpha #intape
cases (sem_seq ????? (sem_adv_mark_r …) 
        (sem_seq ????? (sem_move_l …)
          (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?)) 
            (sem_adv_mark_r alpha))) intape)
#k * #outc * #Hloop whd in ⊢ (%→?);
* #ta * whd in ⊢ (%→?); #Hs1 * #tb * whd in ⊢ (%→?); #Hs2
* #tc * whd in ⊢ (%→%→?); #Hs3 #Hs4
@(ex_intro ?? k) @(ex_intro ?? outc) %
[ @Hloop
| -Hloop #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape
  @(Hs4 … false) -Hs4
  lapply (Hs1 … Hintape) #Hta
  lapply (proj2 … Hs2 … Hta) #Htb
  cases (Hs3 … Htb)
  [ * #Hfalse normalize in Hfalse; destruct (Hfalse)
  | * #_ -Hs3 #Hs3 
    lapply (Hs3 (l1@[〈a,false〉]) 〈x,true〉 l0 ???)
    [ #x1 #Hx1 cases (memb_append … Hx1)
      [ @Hl1
      | #Hx1' >(memb_single … Hx1') % ]
    | % 
    | >associative_append %
    | >reverse_append #Htc @Htc ]
  ]
qed. *)

(* 
   MATCH AND ADVANCE(f)
   
   input:
   l0 x* a l1 x0* a0 l2
              ^
    
   output:
   l0 x a* l1 x0 a0* l2   (f(x0) == true)
        ^
   l0 x* a l1 x0* a0 l2   (f(x0) == false)
              ^
*)

definition match_and_adv ≝ 
  λalpha,f.ifTM ? (test_char ? f)
     (adv_both_marks alpha) (clear_mark ?) tc_true.

definition R_match_and_adv ≝ 
  λalpha,f,t1,t2.
    ∀l0,x,a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
    t1 = midtape (FinProd … alpha FinBool) 
        (l1@〈a,false〉::〈x,true〉::l0) 〈x0,true〉 (〈a0,false〉::l2) → 
    (f 〈x0,true〉 = true ∧ t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (reverse ? l1@〈x0,false〉::〈a0,true〉::l2))
    ∨ (f 〈x0,true〉 = false ∧ 
    t2 = midtape ? (l1@〈a,false〉::〈x,true〉::l0) 〈x0,false〉 (〈a0,false〉::l2)).

lemma sem_match_and_adv : 
  ∀alpha,f.Realize ? (match_and_adv alpha f) (R_match_and_adv alpha f).
#alpha #f #intape
cases (sem_if ? (test_char ? f) … tc_true (sem_test_char ? f) (sem_adv_both_marks alpha) (sem_clear_mark ?) intape)
#k * #outc * #Hloop #Hif @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop
cases Hif
[ * #ta * whd in ⊢ (%→%→?); #Hta #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape >Hintape in Hta; 
  * * #x1 * whd in ⊢ ((??%?)→?); #H destruct (H) #Hf #Hta % % 
  [ @Hf | >append_cons >append_cons in Hta; #Hta @(proj1 ?? (Houtc …) …Hta) 
    [ #x #memx cases (memb_append …memx) 
      [@Hl1 | -memx #memx >(memb_single … memx) %]
    |>reverse_cons >reverse_append % ] ]
| * #ta * whd in ⊢ (%→%→?); #Hta #Houtc
  #l0 #x #a #l1 #x0 #a0 #l2 #Hl1 #Hintape >Hintape in Hta; 
  * #Hf #Hta %2 % [ @Hf % | >(proj2 ?? Houtc … Hta) % ]
]
qed.

definition R_match_and_adv_of ≝ 
  λalpha,t1,t2.current (FinProd … alpha FinBool) t1 = None ? → t2 = t1.

lemma sem_match_and_adv_of : 
  ∀alpha,f.Realize ? (match_and_adv alpha f) (R_match_and_adv_of alpha).
#alpha #f #intape
cases (sem_if ? (test_char ? f) … tc_true (sem_test_char ? f) (sem_adv_both_marks alpha) (sem_clear_mark ?) intape)
#k * #outc * #Hloop #Hif @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop
cases Hif
[ * #ta * whd in ⊢ (%→%→?); #Hta #Houtc #Hcur
  cases Hta * #x >Hcur * #Hfalse destruct (Hfalse)
| * #ta * whd in ⊢ (%→%→?); * #_ #Hta * #Houtc #_ <Hta #Hcur >(Houtc Hcur) % ]
qed.

lemma sem_match_and_adv_full : 
  ∀alpha,f.Realize ? (match_and_adv alpha f) 
    (R_match_and_adv alpha f ∩ R_match_and_adv_of alpha).
#alpha #f #intape cases (sem_match_and_adv ? f intape)
#i * #outc * #Hloop #HR1 %{i} %{outc} % // % //
cases (sem_match_and_adv_of ? f intape) #i0 * #outc0 * #Hloop0 #HR2
>(loop_eq … Hloop Hloop0) //
qed.

(*
 if x = c
      then move_right; ----
           adv_to_mark_r;
           if current (* x0 *) = 0
              then advance_mark ----
                   adv_to_mark_l;
                   advance_mark
              else STOP
      else M
*)

definition comp_step_subcase ≝ λalpha,c,elseM.
  ifTM ? (test_char ? (λx.x == c))
    (move_r … · adv_to_mark_r ? (is_marked alpha) · match_and_adv ? (λx.x == c))
    elseM tc_true.

definition R_comp_step_subcase ≝ 
  λalpha,c,RelseM,t1,t2.
    ∀l0,x,rs.t1 = midtape (FinProd … alpha FinBool) l0 〈x,true〉 rs → 
    (〈x,true〉 = c →
     ((∀c.memb ? c rs = true → is_marked ? c = false) →
       ∀a,l. (a::l) = reverse ? (〈x,true〉::rs) → t2 = rightof (FinProd alpha FinBool) a (l@l0)) ∧
     ∀a,l1,x0,a0,l2. (∀c.memb ? c l1 = true → is_marked ? c = false) → 
     rs = 〈a,false〉::l1@〈x0,true〉::〈a0,false〉::l2 → 
     ((x = x0 →
      t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (l1@〈x0,false〉::〈a0,true〉::l2)) ∧
      (x ≠ x0 →
      t2 = midtape (FinProd … alpha FinBool) 
        (reverse ? l1@〈a,false〉::〈x,true〉::l0) 〈x0,false〉 (〈a0,false〉::l2)))) ∧
    (〈x,true〉 ≠ c → RelseM t1 t2).

lemma dec_marked: ∀alpha,rs. 
 decidable (∀c.memb ? c rs = true → is_marked alpha c = false).
#alpha #rs elim rs 
  [%1 #n normalize #H destruct
  |#a #tl cases (true_or_false (is_marked ? a)) #Ha 
    [#_ %2 % #Hall @(absurd ?? not_eq_true_false) <Ha 
     @Hall @memb_hd 
    |* [#Hall %1 #c #memc cases (orb_true_l … memc) 
         [#eqca >(\P eqca) @Ha |@Hall]
    |#Hnall %2 @(not_to_not … Hnall) #Hall #c #memc @Hall @memb_cons //
    ]
  qed.
  
lemma sem_comp_step_subcase : 
  ∀alpha,c,elseM,RelseM.
  Realize ? elseM RelseM → 
  Realize ? (comp_step_subcase alpha c elseM) 
    (R_comp_step_subcase alpha c RelseM).
#alpha #c #elseM #RelseM #Helse #intape
cases (sem_if ? (test_char ? (λx.x == c)) … tc_true 
        (sem_test_char ? (λx.x == c)) 
        (sem_seq ????? (sem_move_r …)
          (sem_seq ????? (sem_adv_to_mark_r ? (is_marked alpha))
             (sem_match_and_adv_full ? (λx.x == c)))) Helse intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop cases HR -HR
  [* #ta * whd in ⊢ (%→?); #Hta * #tb * whd in ⊢ (%→?); #Htb
   * #tc * whd in ⊢ (%→?); #Htc * whd in ⊢ (%→%→?); #Houtc #Houtc1 
   #l0 #x #rs #Hintape %
     [#_ cases (dec_marked ? rs) #Hdec
      [%
        [#_ #a #l1 
         >Hintape in Hta; * #_(* #x1 * whd in ⊢ ((??%?)→?); #H destruct (H) #Hx *)
         #Hta lapply (proj2 … Htb … Hta) -Htb -Hta cases rs in Hdec;
           [#_ whd in ⊢ ((???%)→?); #Htb >Htb in Htc; #Htc
            lapply (proj1 ?? Htc (refl …)) -Htc #Htc <Htc in Houtc1; #Houtc1
            normalize in ⊢ (???%→?); #Hl1 destruct(Hl1) @(Houtc1 (refl …))
           |#r0 #rs0 #Hdec whd in ⊢ ((???%)→?); #Htb >Htb in Htc; #Htc
            >reverse_cons >reverse_cons #Hl1
            cases (proj2 ?? Htc … (refl …))
            [* >(Hdec …) [ #Hfalse destruct(Hfalse) ] @memb_hd
            |* #_ -Htc #Htc cut (∃l2.l1 = l2@[〈x,true〉])
             [generalize in match Hl1; -Hl1 <(reverse_reverse … l1)
              cases (reverse ? l1)
              [#Hl1 cut ([a]=〈x,true〉::r0::rs0)
               [ <(reverse_reverse … (〈x,true〉::r0::rs0))
                 >reverse_cons >reverse_cons <Hl1 % 
               | #Hfalse destruct(Hfalse)]
              |#a0 #l10 >reverse_cons #Heq
               lapply (append_l2_injective_r ? (a::reverse ? l10) ???? Heq) //
               #Ha0 destruct(Ha0) /2/ ]
             |* #l2 #Hl2 >Hl2 in Hl1; #Hl1 
              lapply (append_l1_injective_r ? (a::l2) … Hl1) // -Hl1 #Hl1
              >reverse_cons in Htc; #Htc lapply (Htc … (sym_eq … Hl1))
              [ #x0 #Hmemb @Hdec @memb_cons @Hmemb ]
              -Htc #Htc >Htc in Houtc1; #Houtc1 >associative_append @Houtc1 % 
             ]
            ]
           ]
        |#a #l1 #x0 #a0 
         #l2 #_ #Hrs @False_ind
         @(absurd ?? not_eq_true_false) 
         change with (is_marked ? 〈x0,true〉) in match true;
         @Hdec >Hrs @memb_cons @memb_append_l2 @memb_hd 
        ]
      |% [#H @False_ind @(absurd …H Hdec)]
       #a #l1 #x0 #a0 #l2 #Hl1 #Hrs >Hrs in Hintape; #Hintape
       >Hintape in Hta; * * #x1 * whd in ⊢ ((??%?)→?); #H destruct (H) #Hx
       #Hta lapply (proj2 … Htb … Hta) -Htb -Hta 
       whd in match (mk_tape ????); #Htb cases Htc -Htc #_ #Htc
       cases (Htc … Htb) [ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
       -Htc * * #_ #Htc #_ lapply (Htc l1 〈x0,true〉 (〈a0,false〉::l2) (refl ??) (refl ??) Hl1)
       -Htc #Htc cases (Houtc ???????? Htc) -Houtc
        [* #Hx0 #Houtc %
          [ #Hx >Houtc >reverse_reverse %
          | lapply (\P Hx0) -Hx0 <(\P Hx) in ⊢ (%→?); #Hx0 destruct (Hx0)
            * #Hfalse @False_ind @Hfalse % ]
        |* #Hx0 #Houtc %
          [ #Hxx0 >Hxx0 in Hx; #Hx; lapply (\Pf Hx0) -Hx0 <(\P Hx) in ⊢ (%→?);
            * #Hfalse @False_ind @Hfalse %
          | #_ >Houtc % ] 
        |#c #membc @Hl1 <(reverse_reverse …l1) @memb_reverse @membc
        ]
       ]
     | cases Hta * #c0 * >Hintape whd in ⊢ (??%%→?); #Hc0 destruct(Hc0) #Hx >(\P Hx)
       #_ * #Hc @False_ind @Hc % ]
    | * #ta * * #Hcur #Hta #Houtc
      #l0 #x #rs #Hintape >Hintape in Hcur; #Hcur lapply (Hcur ? (refl …)) -Hcur #Hc %
      [ #Hfalse >Hfalse in Hc; #Hc cases (\Pf Hc) #Hc @False_ind @Hc %
      | -Hc #Hc <Hintape <Hta @Houtc ] ]
qed.

(* 
- se marcato, itero
- se non è marcato
  + se è un bit, ho fallito il confronto della tupla corrente
  + se è un separatore, la tupla fa match


ifTM ? (test_char ? is_marked)
  (single_finalTM … (comp_step_subcase unialpha 〈bit false,true〉
    (comp_step_subcase unialpha 〈bit true,true〉
      (clear_mark …))))
  (nop ?)
*)

definition comp_step ≝ 
  ifTM ? (test_char ? (is_marked ?))
  (single_finalTM … (comp_step_subcase FSUnialpha 〈bit false,true〉
    (comp_step_subcase FSUnialpha 〈bit true,true〉
      (comp_step_subcase FSUnialpha 〈null,true〉
        (clear_mark …)))))
  (nop ?)
  tc_true.

(* da spostare *)

lemma mem_append : ∀A,x,l1,l2. mem A x (l1@l2) → 
  mem A x l1 ∨ mem A x l2.
#A #x #l1 elim l1 normalize [/2/]
#a #tl #Hind #l2 * [#eqxa %1 /2/ |#memx cases (Hind … memx) /3/]
qed.

let rec split_on A (l:list A) f acc on l ≝ 
  match l with 
  [ nil ⇒ 〈acc,nil ?〉
  | cons a tl ⇒ 
    if f a then 〈acc,a::tl〉 else split_on A tl f (a::acc) 
  ].
  
lemma split_on_spec: ∀A,l,f,acc,res1,res2.
  split_on A l f acc = 〈res1,res2〉 → 
    (∃l1. res1 = l1@acc ∧
    reverse ? l1@res2 = l ∧ 
    ∀x. mem ? x l1 → f x = false) ∧ 
    ∀a,tl. res2 = a::tl → f a = true.
#A #l #f elim l
  [#acc #res1 #res2 normalize in ⊢ (%→?); #H destruct % 
    [@(ex_intro … []) % normalize [% % | #x @False_ind]
    |#a #tl #H destruct
    ]
  |#a #tl #Hind #acc #res1 #res2 normalize in ⊢ (%→?);
   cases (true_or_false (f a)) #Hfa >Hfa normalize in ⊢ (%→?);
   #H destruct
   [% [@(ex_intro … []) % normalize [% % | #x @False_ind]
      |#a1 #tl1 #H destruct (H) //]
   |cases (Hind (a::acc) res1 res2 H) * #l1 * *
    #Hres1 #Htl #Hfalse #Htrue % [2:@Htrue] @(ex_intro … (l1@[a])) % 
     [% [>associative_append @Hres1 | >reverse_append <Htl % ]
     |#x #Hmemx cases (mem_append ???? Hmemx) 
        [@Hfalse | normalize * [#H >H //| @False_ind]
     ]
   ]
  ]
qed.

axiom mem_reverse: ∀A,l,x. mem A x (reverse ? l) → mem A x l.

lemma split_on_spec_ex: ∀A,l,f.∃l1,l2.
    l1@l2 = l ∧ (∀x:A. mem ? x l1 → f x = false) ∧ 
    ∀a,tl. l2 = a::tl → f a = true.
#A #l #f @(ex_intro … (reverse … (\fst (split_on A l f [])))) 
@(ex_intro … (\snd (split_on A l f []))) 
cases (split_on_spec A l f [ ] ?? (eq_pair_fst_snd …)) * #l1 * *
>append_nil #Hl1 >Hl1 #Hl #Hfalse #Htrue % 
  [% [@Hl|#x #memx @Hfalse @mem_reverse //] | @Htrue]
qed.

FAIL

(* manca il caso in cui alla destra della testina il nastro non ha la forma
   (l1@〈c0,true〉::〈a0,false〉::l2) 
*)
definition R_comp_step_true ≝ λt1,t2.
  ∃l0,c,a,l1,c0,l1',a0,l2.
    t1 = midtape (FinProd … FSUnialpha FinBool) 
      l0 〈c,true〉 (l1@〈c0,true〉::〈a0,false〉::l2) ∧
       l1@[〈c0,false〉] = 〈a,false〉::l1' ∧
      (∀c.memb ? c l1 = true → is_marked ? c = false) ∧
      (bit_or_null c = true → c0 = c →
        t2 = midtape ? (〈c,false〉::l0) 〈a,true〉 (l1'@〈c0,false〉::〈a0,true〉::l2)) ∧
      (bit_or_null c = true → c0 ≠ c →
        t2 = midtape (FinProd … FSUnialpha FinBool) 
         (reverse ? l1@〈a,false〉::〈c,true〉::l0) 〈c0,false〉 (〈a0,false〉::l2)) ∧ 
      (bit_or_null c = false → 
        t2 = midtape ? l0 〈c,false〉 (〈a,false〉::l1@〈c0,true〉::〈a0,false〉::l2)).

definition R_comp_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   is_marked ? c = false ∧ t2 = t1.

(*
lemma is_marked_to_exists: ∀alpha,c. is_marked alpha c = true →
 ∃c'. c = 〈c',true〉.
#alpha * c *)

lemma sem_comp_step : 
  accRealize ? comp_step (inr … (inl … (inr … start_nop))) 
    R_comp_step_true R_comp_step_false.
@(acc_sem_if_app … (sem_test_char ? (is_marked ?))
        (sem_comp_step_subcase FSUnialpha 〈bit false,true〉 ??
          (sem_comp_step_subcase FSUnialpha 〈bit true,true〉 ?? 
            (sem_comp_step_subcase FSUnialpha 〈null,true〉 ?? 
              (sem_clear_mark …))))
        (sem_nop …) …)
(*        
[#intape #outtape #midtape * * * #c #b * #Hcurrent 
whd in ⊢ ((??%?)→?); #Hb #Hmidtape >Hmidtape -Hmidtape
 cases (current_to_midtape … Hcurrent) #ls * #rs >Hb #Hintape >Hintape -Hb
 whd in ⊢ (%→?); #Htapea lapply (Htapea … (refl …)) -Htapea
 cases (split_on_spec_ex ? rs (is_marked ?)) #l1 * #l2 * * #Hrs #Hl1 #Hl2
 cases (true_or_false (c == bit false))
  [(* c = bit false *) #Hc * 
   [>(\P Hc) #H lapply (H (refl ??)) -H * #_ #H lapply (H ????? Hl1) @False_ind @H //]
   * #_ #Hout whd 
   cases (split_on_spec *)
[ #ta #tb #tc * * * #c #b * #Hcurrent whd in ⊢(??%?→?); #Hc 
  >Hc in Hcurrent; #Hcurrent; #Htc
  cases (current_to_midtape … Hcurrent) #ls * #rs #Hta
  >Htc #H1 cases (H1 … Hta) -H1 #H1 #H2 whd
  lapply (refl ? (〈c,true〉==〈bit false,true〉)) 
  cases (〈c,true〉==〈bit false,true〉) in ⊢ (???%→?);
  [ #Hceq lapply (H1 (\P Hceq)) -H1 *
    cases (split_on_spec_ex ? rs (is_marked ?)) #l1 * #l2 * * cases l2
    [ >append_nil #Hrs #Hl1 #Hl2 #Htb1 #_

 #Hstate lapply (H1 Hstate) -H1 -Hstate -H2 *
  #ta * whd in ⊢ (%→?); #Hleft #Hright #ls #c #rs #Hintape
  >Hintape in Hleft; * *  
  cases c in Hintape; #c' #b #Hintape #x * whd in ⊢ (??%?→?); #H destruct (H) 
  whd in ⊢ (??%?→?); #Hb >Hb #Hta @(ex_intro ?? c') % //
  cases (Hright … Hta)
  [ * #Hc' #H1 % % [destruct (Hc') % ]
    #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
    cases (H1 … Hl1 Hrs)
    [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
    | * #Hneq #Houtc %2 %
      [ @sym_not_eq //
      | @Houtc ]
    ]
  | * #Hc #Helse1 cases (Helse1 … Hta)
    [ * #Hc' #H1 % % [destruct (Hc') % ]
      #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
      cases (H1 … Hl1 Hrs)
      [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
      | * #Hneq #Houtc %2 %
        [ @sym_not_eq //
        | @Houtc ]
      ]
    | * #Hc' #Helse2 cases (Helse2 … Hta)
      [ * #Hc'' #H1 % % [destruct (Hc'') % ]
        #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
        cases (H1 … Hl1 Hrs)
        [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
        | * #Hneq #Houtc %2 %
          [ @sym_not_eq //
          | @Houtc ]
        ]
      | * #Hc'' whd in ⊢ (%→?); #Helse3 %2 %
        [ generalize in match Hc''; generalize in match Hc'; generalize in match Hc;
          cases c'
          [ * [ #_ #Hfalse @False_ind @(absurd ?? Hfalse) %
              | #Hfalse @False_ind @(absurd ?? Hfalse) % ]
          | #_ #_ #Hfalse @False_ind @(absurd ?? Hfalse) %
          |*: #_ #_ #_ % ]
        | @(Helse3 … Hta)
        ]
      ]
    ]
  ]
| #Hstate lapply (H2 Hstate) -H1 -Hstate -H2 *
  #ta * whd in ⊢ (%→%→?); #Hleft #Hright #ls #c #rs #Hintape
  >Hintape in Hleft; * #Hc #Hta % [@Hc % | >Hright //]
]
qed.
definition R_comp_step_true ≝ 
  λt1,t2.
    ∀l0,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) l0 c rs → 
    ∃c'. c = 〈c',true〉 ∧
    ((bit_or_null c' = true ∧
     ∀a,l1,c0,a0,l2.
      rs = 〈a,false〉::l1@〈c0,true〉::〈a0,false〉::l2 → 
      (∀c.memb ? c l1 = true → is_marked ? c = false) → 
      (c0 = c' ∧
       t2 = midtape ? (〈c',false〉::l0) 〈a,true〉 (l1@〈c0,false〉::〈a0,true〉::l2)) ∨
      (c0 ≠ c' ∧
       t2 = midtape (FinProd … FSUnialpha FinBool) 
        (reverse ? l1@〈a,false〉::〈c',true〉::l0) 〈c0,false〉 (〈a0,false〉::l2))) ∨
     (bit_or_null c' = false ∧ t2 = midtape ? l0 〈c',false〉 rs)).

definition R_comp_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   is_marked ? c = false ∧ t2 = t1.
   
lemma sem_comp_step : 
  accRealize ? comp_step (inr … (inl … (inr … start_nop))) 
    R_comp_step_true R_comp_step_false.
#intape
cases (acc_sem_if … (sem_test_char ? (is_marked ?))
        (sem_comp_step_subcase FSUnialpha 〈bit false,true〉 ??
          (sem_comp_step_subcase FSUnialpha 〈bit true,true〉 ?? 
            (sem_comp_step_subcase FSUnialpha 〈null,true〉 ?? 
              (sem_clear_mark …))))
        (sem_nop …) intape)
#k * #outc * * #Hloop #H1 #H2
@(ex_intro ?? k) @(ex_intro ?? outc) %
[ % [@Hloop ] ] -Hloop
[ #Hstate lapply (H1 Hstate) -H1 -Hstate -H2 *
  #ta * whd in ⊢ (%→?); #Hleft #Hright #ls #c #rs #Hintape
  >Hintape in Hleft; * *  
  cases c in Hintape; #c' #b #Hintape #x * whd in ⊢ (??%?→?); #H destruct (H) 
  whd in ⊢ (??%?→?); #Hb >Hb #Hta @(ex_intro ?? c') % //
  cases (Hright … Hta)
  [ * #Hc' #H1 % % [destruct (Hc') % ]
    #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
    cases (H1 … Hl1 Hrs)
    [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
    | * #Hneq #Houtc %2 %
      [ @sym_not_eq //
      | @Houtc ]
    ]
  | * #Hc #Helse1 cases (Helse1 … Hta)
    [ * #Hc' #H1 % % [destruct (Hc') % ]
      #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
      cases (H1 … Hl1 Hrs)
      [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
      | * #Hneq #Houtc %2 %
        [ @sym_not_eq //
        | @Houtc ]
      ]
    | * #Hc' #Helse2 cases (Helse2 … Hta)
      [ * #Hc'' #H1 % % [destruct (Hc'') % ]
        #a #l1 #c0 #a0 #l2 #Hrs >Hrs in Hintape; #Hintape #Hl1
        cases (H1 … Hl1 Hrs)
        [ * #Htmp >Htmp -Htmp #Houtc % % // @Houtc
        | * #Hneq #Houtc %2 %
          [ @sym_not_eq //
          | @Houtc ]
        ]
      | * #Hc'' whd in ⊢ (%→?); #Helse3 %2 %
        [ generalize in match Hc''; generalize in match Hc'; generalize in match Hc;
          cases c'
          [ * [ #_ #Hfalse @False_ind @(absurd ?? Hfalse) %
              | #Hfalse @False_ind @(absurd ?? Hfalse) % ]
          | #_ #_ #Hfalse @False_ind @(absurd ?? Hfalse) %
          |*: #_ #_ #_ % ]
        | @(Helse3 … Hta)
        ]
      ]
    ]
  ]
| #Hstate lapply (H2 Hstate) -H1 -Hstate -H2 *
  #ta * whd in ⊢ (%→%→?); #Hleft #Hright #ls #c #rs #Hintape
  >Hintape in Hleft; * #Hc #Hta % [@Hc % | >Hright //]
]
qed.

definition compare ≝ 
  whileTM ? comp_step (inr … (inl … (inr … start_nop))).

(*
definition R_compare :=
  λt1,t2.
  (t
  
  ∀ls,c,b,rs.t1 = midtape ? ls 〈c,b〉 rs →
  (b = true → rs = ....) → 
  (b = false ∧ ....) ∨
  (b = true ∧ 
   
   rs = cs@l1@〈c0,true〉::cs0@l2
   (
 
  
  ls 〈c,b〉 cs l1 〈c0,b0〉 cs0 l2
  

ACCETTAZIONE:  
  ls (hd (Ls@〈grid,false〉))* (tail (Ls@〈grid,false〉)) l1 (hd (Ls@〈comma,false〉))* (tail (Ls@〈comma,false〉)) l2
     ^^^^^^^^^^^^^^^^^^^^^^^
  
  ls Ls 〈grid,false〉 l1 Ls 〈comma,true〉 l2
        ^^^^^^^^^^^^

RIFIUTO: c ≠ d
  
  ls (hd (Ls@〈c,false〉))* (tail (Ls@〈c,false〉)) l1 (hd (Ls@〈d,false〉))* (tail (Ls@〈d,false〉)) l2
     ^^^^^^^^^^^^^^^^^^^^^^^
  
  
  ls Ls 〈c,true〉 l1 Ls 〈d,false〉 l2
                       ^^^^^^^^
  
  ).
  
  |bs| = |b0s| → 
  (∃la,d.〈b,true〉::bs = la@[〈grid,d〉] ∧ ∀x.memb ? x la → is_bit (\fst x) = true) → 
  (∃lb,d0.〈b0,true〉::b0s = lb@[〈comma,d0〉] ∧ ∀x.memb ? x lb → is_bit (\fst x) = true) → 
  t1 = midtape ? l0 〈b,true〉 (bs@l1@〈b0,true〉::b0s@l2 → 
  
  mk_tape left (option current) right
  
  (b = grid ∧ b0 = comma ∧ bs = [] ∧ b0s = [] ∧
   t2 = midtape ? l0 〈grid,false〉 (l1@〈comma,true〉::l2)) ∨
  (b = bit x ∧ b = c ∧ bs = b0s
  *)
definition R_compare :=
  λt1,t2.
  ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
  (∀c'.bit_or_null c' = false → c = 〈c',true〉 → t2 = midtape ? ls 〈c',false〉 rs) ∧
  (∀c'. c = 〈c',false〉 → t2 = t1) ∧
  ∀b,b0,bs,b0s,l1,l2.
  |bs| = |b0s| → 
  (∀c.memb (FinProd … FSUnialpha FinBool) c bs = true → bit_or_null (\fst c) = true) → 
  (∀c.memb (FinProd … FSUnialpha FinBool) c b0s = true → bit_or_null (\fst c) = true) → 
  (∀c.memb ? c bs = true → is_marked ? c = false) → 
  (∀c.memb ? c b0s = true → is_marked ? c = false) → 
  (∀c.memb ? c l1 = true → is_marked ? c = false) → 
  c = 〈b,true〉 → bit_or_null b = true → 
  rs = bs@〈grid,false〉::l1@〈b0,true〉::b0s@〈comma,false〉::l2 → 
  (〈b,true〉::bs = 〈b0,true〉::b0s ∧
   t2 = midtape ? (reverse ? bs@〈b,false〉::ls)
          〈grid,false〉 (l1@〈b0,false〉::b0s@〈comma,true〉::l2)) ∨
  (∃la,c',d',lb,lc.c' ≠ d' ∧
    〈b,false〉::bs = la@〈c',false〉::lb ∧
    〈b0,false〉::b0s = la@〈d',false〉::lc ∧
    t2 = midtape (FinProd … FSUnialpha FinBool) (reverse ? la@
                    reverse ? l1@
                    〈grid,false〉::
                    reverse ? lb@
                    〈c',true〉::
                    reverse ? la@ls)
                    〈d',false〉 (lc@〈comma,false〉::l2)).
                    
lemma wsem_compare : WRealize ? compare R_compare.
#t #i #outc #Hloop
lapply (sem_while ?????? sem_comp_step t i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea whd in ⊢ (%→?); #Rfalse #ls #c #rs #Htapea %
  [ %
    [ #c' #Hc' #Hc lapply (Rfalse … Htapea) -Rfalse * >Hc
      whd in ⊢ (??%?→?); #Hfalse destruct (Hfalse)
    | #c' #Hc lapply (Rfalse … Htapea) -Rfalse * #_
      #Htrue @Htrue ]
  | #b #b0 #bs #b0s #l1 #l2 #Hlen #Hbs1 #Hb0s1 #Hbs2 #Hb0s2 #Hl1 #Hc
    cases (Rfalse … Htapea) -Rfalse >Hc whd in ⊢ (??%?→?);#Hfalse destruct (Hfalse)
  ]
| #tapea #tapeb #tapec #Hleft #Hright #IH #Htapec lapply (IH Htapec) -Htapec -IH #IH
  whd in Hleft; #ls #c #rs #Htapea cases (Hleft … Htapea) -Hleft
  #c' * #Hc >Hc cases (true_or_false (bit_or_null c')) #Hc'
  [2: * 
    [ * >Hc' #H @False_ind destruct (H)
    | * #_ #Htapeb cases (IH … Htapeb) * #_ #H #_ %
      [% 
        [#c1 #Hc1 #Heqc destruct (Heqc) <Htapeb @(H c1) %
        |#c1 #Hfalse destruct (Hfalse)
        ]
      |#b #b0 #bs #b0s #l1 #l2 #_ #_ #_ #_ #_ #_
       #Heq destruct (Heq) >Hc' #Hfalse @False_ind destruct (Hfalse)
      ]
    ]
 |#Hleft %
    [ %
      [ #c'' #Hc'' #Heq destruct (Heq) >Hc'' in Hc'; #H destruct (H) 
      | #c0 #Hfalse destruct (Hfalse)
      ]
    |#b #b0 #bs #b0s #l1 #l2 #Hlen #Hbs1 #Hb0s1 #Hbs2 #Hb0s2 #Hl1
     #Heq destruct (Heq) #_ #Hrs cases Hleft -Hleft
      [2: * >Hc' #Hfalse @False_ind destruct ] * #_
       @(list_cases2 … Hlen)
       [ #Hbs #Hb0s generalize in match Hrs; >Hbs in ⊢ (%→?); >Hb0s in ⊢ (%→?);
       -Hrs #Hrs normalize in Hrs; #Hleft cases (Hleft ????? Hrs ?) -Hleft
         [ * #Heqb #Htapeb cases (IH … Htapeb) -IH * #IH #_ #_
          % %
            [ >Heqb >Hbs >Hb0s %
            | >Hbs >Hb0s @IH %
            ] 
         |* #Hneqb #Htapeb %2
          @(ex_intro … [ ]) @(ex_intro … b)
          @(ex_intro … b0) @(ex_intro … [ ]) 
          @(ex_intro … [ ]) %
            [ % [ % [@sym_not_eq //| >Hbs %] | >Hb0s %]
            | cases (IH … Htapeb) -IH * #_ #IH #_ >(IH ? (refl ??))
              @Htapeb
            ]
         | @Hl1 ]
      | * #b' #bitb' * #b0' #bitb0' #bs' #b0s' #Hbs #Hb0s 
        generalize in match Hrs; >Hbs in ⊢ (%→?); >Hb0s in ⊢ (%→?);
        cut (bit_or_null b' = true ∧ bit_or_null b0' = true ∧ 
             bitb' = false ∧ bitb0' = false)
        [ % [ % [ % [ >Hbs in Hbs1; #Hbs1 @(Hbs1 〈b',bitb'〉) @memb_hd
            | >Hb0s in Hb0s1; #Hb0s1 @(Hb0s1 〈b0',bitb0'〉) @memb_hd ]
            | >Hbs in Hbs2; #Hbs2 @(Hbs2 〈b',bitb'〉) @memb_hd ]
            | >Hb0s in Hb0s2; #Hb0s2 @(Hb0s2 〈b0',bitb0'〉) @memb_hd ]
        | * * * #Ha #Hb #Hc #Hd >Hc >Hd
          #Hrs #Hleft 
          cases (Hleft b' (bs'@〈grid,false〉::l1) b0 b0' 
                         (b0s'@〈comma,false〉::l2) ??) -Hleft
          [ 3: >Hrs normalize @eq_f >associative_append %
          | * #Hb0 #Htapeb cases (IH …Htapeb) -IH * #_ #_ #IH
            cases (IH b' b0' bs' b0s' (l1@[〈b0,false〉]) l2 ??????? Ha ?) -IH
            [ * #Heq #Houtc % %
              [ >Hb0 @eq_f >Hbs in Heq; >Hb0s in ⊢ (%→?); #Heq
                destruct (Heq) >Hb0s >Hc >Hd %
              | >Houtc >Hbs >Hb0s >Hc >Hd >reverse_cons >associative_append
                >associative_append %
              ]
            | * #la * #c' * #d' * #lb * #lc * * * #H1 #H2 #H3 #H4 %2
              @(ex_intro … (〈b,false〉::la)) @(ex_intro … c') @(ex_intro … d')
              @(ex_intro … lb) @(ex_intro … lc)
              % [ % [ % // >Hbs >Hc >H2 % | >Hb0s >Hd >H3 >Hb0 % ] 
                | >H4 >Hbs >Hb0s >Hc >Hd >Hb0 >reverse_append
                  >reverse_cons >reverse_cons
                  >associative_append >associative_append
                  >associative_append >associative_append %
                ]
            | generalize in match Hlen; >Hbs >Hb0s
              normalize #Hlen destruct (Hlen) @e0
            | #c0 #Hc0 @Hbs1 >Hbs @memb_cons // 
            | #c0 #Hc0 @Hb0s1 >Hb0s @memb_cons // 
            | #c0 #Hc0 @Hbs2 >Hbs @memb_cons // 
            | #c0 #Hc0 @Hb0s2 >Hb0s @memb_cons // 
            | #c0 #Hc0 cases (memb_append … Hc0) 
              [ @Hl1 | #Hc0' >(memb_single … Hc0') % ]
            | %
            | >associative_append >associative_append % ]
         | * #Hneq #Htapeb %2
            @(ex_intro … []) @(ex_intro … b) @(ex_intro … b0)
            @(ex_intro … bs) @(ex_intro … b0s) %
           [ % // % // @sym_not_eq // 
           | >Hbs >Hb0s >Hc >Hd >reverse_cons >associative_append
             >reverse_append in Htapeb; >reverse_cons
             >associative_append >associative_append
             #Htapeb <Htapeb
             cases (IH … Htapeb) -Htapeb -IH * #_ #IH #_ @(IH ? (refl ??))
           ]
         | #c1 #Hc1 cases (memb_append … Hc1) #Hyp
           [ @Hbs2 >Hbs @memb_cons @Hyp
           | cases (orb_true_l … Hyp)
             [ #Hyp2 >(\P Hyp2) %
             | @Hl1
             ]
           ]
         ]
]]]]]
qed.       

axiom sem_compare : Realize ? compare R_compare.
