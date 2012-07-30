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

definition R_adv_both_marks ≝ λalpha,t1,t2.
  ∀ls,x0,rs.
    t1 = midtape (FinProd … alpha FinBool) ls 〈x0,true〉 rs →   
     (rs = [ ] → (* first case: rs empty *)
       t2 = rightof (FinProd … alpha FinBool) 〈x0,false〉 ls) ∧       
     (∀l0,x,a,a0,b,l1,l1',l2. 
       ls = (l1@〈x,true〉::l0) →
       (∀c.memb ? c l1 = true → is_marked ? c = false) → 
       rs = (〈a0,b〉::l2) →
       reverse ? (〈x0,false〉::l1) = 〈a,false〉::l1' →
       t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (l1'@〈a0,true〉::l2)).

lemma sem_adv_both_marks :
  ∀alpha.Realize ? (adv_both_marks alpha) (R_adv_both_marks alpha).    
#alpha 
@(sem_seq_app … (sem_adv_mark_r …) 
   (sem_seq ????? (sem_move_l …)
      (sem_seq ????? (sem_adv_to_mark_l ? (is_marked ?)) 
        (sem_adv_mark_r alpha))) …)
#intape #outtape * #tapea * #Hta * #tb * #Htb * #tc * #Htc #Hout
#ls #c #rs #Hintape %
  [#Hrs >Hrs in Hintape; #Hintape lapply (proj2 ?? (proj1 ?? Hta … ) … Hintape) -Hta #Hta
   lapply (proj1 … Htb) >Hta -Htb #Htb lapply (Htb (refl …)) -Htb #Htb 
   lapply (proj1 ?? Htc) <Htb -Htc #Htc lapply (Htc (refl …)) -Htc #Htc
   @sym_eq >Htc @(proj2 ?? Hout …) <Htc %
  |#l0 #x #a #a0 #b #l1 #l1' #l2 #Hls #Hmarks #Hrs #Hrev 
   >Hrs in Hintape; >Hls #Hintape
   @(proj1 ?? (proj1 ?? Hout … ) ? false) -Hout
   lapply (proj1 … (proj1 … Hta …) … Hintape) #Htapea
   lapply (proj2 … Htb  … Htapea) -Htb
   whd in match (mk_tape ????) ; #Htapeb 
   lapply (proj1 ?? (proj2 ?? (proj2 ?? Htc … Htapeb) (refl …))) -Htc #Htc
   change with ((?::?)@?) in match (cons ???); <Hrev >reverse_cons
   >associative_append @Htc [%|%|@Hmarks]
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
    ∀ls,x0,rs.
     t1 = midtape (FinProd … alpha FinBool) ls 〈x0,true〉 rs →   
    ((* first case: (f 〈x0,true〉 = false) *)
     (f 〈x0,true〉 = false) → 
       t2 = midtape (FinProd … alpha FinBool) ls 〈x0,false〉 rs) ∧   
    ((f 〈x0,true〉 = true) →  rs = [ ] → (* second case: rs empty *)
       t2 = rightof (FinProd … alpha FinBool) 〈x0,false〉 ls) ∧       
    ((f 〈x0,true〉 = true) →  
     ∀l0,x,a,a0,b,l1,l1',l2. 
     (* third case: we expect to have a mark on the left! *)
     ls = (l1@〈x,true〉::l0) → 
     (∀c.memb ? c l1 = true → is_marked ? c = false) → 
     rs = 〈a0,b〉::l2 →
     reverse ? (〈x0,false〉::l1) = 〈a,false〉::l1' →
       t2 = midtape ? (〈x,false〉::l0) 〈a,true〉 (l1'@〈a0,true〉::l2)).

lemma sem_match_and_adv : 
  ∀alpha,f.Realize ? (match_and_adv alpha f) (R_match_and_adv alpha f).
#alpha #f #intape
cases (sem_if ? (test_char ? f) … tc_true (sem_test_char ? f) (sem_adv_both_marks alpha) (sem_clear_mark ?) intape)
#k * #outc * #Hloop #Hif @(ex_intro ?? k) @(ex_intro ?? outc)
% [ @Hloop ] -Hloop
(* 
@(sem_if_app … (sem_test_char ? f) (sem_adv_both_marks alpha) (sem_clear_mark ?))
#intape #outape #Htb * #H *)
cases Hif -Hif
[ * #ta * whd in ⊢ (%→%→?); * * #c * #Hcurrent #fc #Hta #Houtc
  #ls #x #rs #Hintape >Hintape in Hcurrent; whd in ⊢ ((??%?)→?); #H destruct (H) %
  [%[>fc #H destruct (H) 
    |#_ #Hrs >Hrs in Hintape; #Hintape >Hintape in Hta; #Hta
     cases (Houtc … Hta) #Houtc #_ @Houtc //
    ]
  |#l0 #x0 #a #a0 #b #l1 #l1' #l2 #Hls #Hmarks #Hrs #Hrev >Hintape in Hta; #Hta
   @(proj2 ?? (Houtc … Hta) … Hls Hmarks Hrs Hrev)
  ]
| * #ta * * #H #Hta * #_ #Houtc #ls #c #rs #Hintape 
   >Hintape in H; #H lapply(H … (refl …)) #fc %
  [%[#_ >Hintape in Hta; #Hta @(Houtc … Hta)
    |>fc #H destruct (H)
    ]
  |>fc #H destruct (H)
  ]
]
qed.

(*
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
*)

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
    ∀ls,x,rs.t1 = midtape (FinProd … alpha FinBool) ls 〈x,true〉 rs → 
    (〈x,true〉 = c →
     ((* test true but no marks in rs *)
      (∀c.memb ? c rs = true → is_marked ? c = false) →
       ∀a,l. (a::l) = reverse ? (〈x,true〉::rs) → 
       t2 = rightof (FinProd alpha FinBool) a (l@ls)) ∧ 
    ∀l1,x0,l2. 
     (∀c.memb ? c l1 = true → is_marked ? c = false) → 
      rs = l1@〈x0,true〉::l2 → 
      (x = x0 → 
       l2 = [ ] → (* test true but l2 is empty *) 
       t2 = rightof ? 〈x0,false〉 ((reverse ? l1)@〈x,true〉::ls))  ∧
      (x = x0 →
       ∀a,a0,b,l1',l2'. (* test true and l2 is not empty *) 
       〈a,false〉::l1' = l1@[〈x0,false〉] →
       l2 = 〈a0,b〉::l2' →
       t2 = midtape ? (〈x,false〉::ls) 〈a,true〉 (l1'@〈a0,true〉::l2')) ∧
      (x ≠ x0 →(* test false *)
      t2 = midtape (FinProd … alpha FinBool) ((reverse ? l1)@〈x,true〉::ls) 〈x0,false〉 l2)) ∧
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

(* axiom daemon:∀P:Prop.P. *)

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
  [* #ta * whd in ⊢ (%→?); * * #cin * #Hcin #Hcintrue #Hta * #tb * whd in ⊢ (%→?); #Htb
   * #tc * whd in ⊢ (%→?); #Htc * whd in ⊢ (%→%→?); #Houtc #Houtc1
   #ls #x #rs #Hintape >Hintape in Hcin; whd in ⊢ ((??%?)→?); #H destruct (H) %
    [#_ cases (dec_marked ? rs) #Hdec
      [%
        [#_ #a #l1 
         >Hintape in Hta; #Hta
         lapply (proj2 ?? Htb … Hta) -Htb -Hta cases rs in Hdec;
           (* by cases on rs *)
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
        |#l1 #x0 #l2 #_ #Hrs @False_ind
         @(absurd ?? not_eq_true_false) 
         change with (is_marked ? 〈x0,true〉) in match true;
         @Hdec >Hrs @memb_append_l2 @memb_hd 
        ]
      |% [#H @False_ind @(absurd …H Hdec)]
       (* by cases on l1 *) *
        [#x0 #l2 #Hdec normalize in ⊢ (%→?); #Hrs >Hrs in Hintape; #Hintape
         >Hintape in Hta; (* * * #x1 * whd in ⊢ ((??%?)→?); #H destruct (H) #Hx *)
         #Hta lapply (proj2 … Htb … Hta) -Htb -Hta 
         whd in match (mk_tape ????); whd in match (tail ??); #Htb cases Htc -Htc
         #_ #Htc cases (Htc … Htb) -Htc 
          [2: * * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
         * * #Htc >Htb in Htc; -Htb #Htc cases (Houtc … Htc) -Houtc * 
         #H1 #H2 #H3 cases (true_or_false (x==x0)) #eqxx0
          [>(\P eqxx0) % [2: #H @False_ind /2/] %
            [#_ #Hl2 >(H2 … Hl2) <(\P eqxx0) [% | @Hcintrue] 
            |#_ #a #a0 #b #l1' #l2' normalize in ⊢ (%→?); #Hdes destruct (Hdes)
             #Hl2 @(H3 … Hdec … Hl2) <(\P eqxx0) [@Hcintrue | % | @reverse_single]
            ]
          |% [% #eqx @False_ind lapply (\Pf eqxx0) #Habs @(absurd … eqx Habs)] 
           #_ @H1 @(\bf ?) @(not_to_not ??? (\Pf eqxx0)) <(\P Hcintrue) 
           #Hdes destruct (Hdes) %
          ]
        |#l1hd #l1tl #x0 #l2 #Hdec normalize in ⊢ (%→?); #Hrs >Hrs in Hintape; #Hintape
         >Hintape in Hta; (* * * #x1 * whd in ⊢ ((??%?)→?); #H destruct (H) #Hx *)
         #Hta lapply (proj2 … Htb … Hta) -Htb -Hta 
         whd in match (mk_tape ????); whd in match (tail ??); #Htb cases Htc -Htc
         #_ #Htc cases (Htc … Htb) -Htc 
          [* #Hfalse @False_ind >(Hdec … (memb_hd …)) in Hfalse; #H destruct] 
         * * #_ #Htc lapply (Htc … (refl …) (refl …) ?) -Htc
          [#x1 #membx1 @Hdec @memb_cons @membx1] #Htc
         cases (Houtc … Htc) -Houtc * 
         #H1 #H2 #H3 #_ cases (true_or_false (x==x0)) #eqxx0
          [>(\P eqxx0) % [2: #H @False_ind /2/] %
            [#_ #Hl2 >(H2 … Hl2) <(\P eqxx0) 
              [>reverse_cons >associative_append % | @Hcintrue] 
            |#_ #a #a0 #b #l1' #l2' normalize in ⊢ (%→?); #Hdes (* destruct (Hdes) *)
             #Hl2 @(H3 ?????? (reverse … (l1hd::l1tl)) … Hl2) <(\P eqxx0) 
              [@Hcintrue 
              |>reverse_cons >associative_append % 
              |#c0 #memc @Hdec <(reverse_reverse ? (l1hd::l1tl)) @memb_reverse @memc
              |>Hdes >reverse_cons >reverse_reverse >(\P eqxx0) %
              ]
            ]
          |% [% #eqx @False_ind lapply (\Pf eqxx0) #Habs @(absurd … eqx Habs)] 
           #_ >reverse_cons >associative_append @H1 @(\bf ?) 
           @(not_to_not ??? (\Pf eqxx0)) <(\P Hcintrue) #Hdes 
           destruct (Hdes) %
          ]
        ]
      ]
    |>(\P Hcintrue) * #Hfalse @False_ind @Hfalse %
    ]
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
  
lemma split_on_spec: ∀A:DeqSet.∀l,f,acc,res1,res2.
  split_on A l f acc = 〈res1,res2〉 → 
    (∃l1. res1 = l1@acc ∧
    reverse ? l1@res2 = l ∧ 
    ∀x. memb ? x l1 =true → f x = false) ∧ 
    ∀a,tl. res2 = a::tl → f a = true.
#A #l #f elim l
  [#acc #res1 #res2 normalize in ⊢ (%→?); #H destruct % 
    [@(ex_intro … []) % normalize [% % | #x #H destruct]
    |#a #tl #H destruct
    ]
  |#a #tl #Hind #acc #res1 #res2 normalize in ⊢ (%→?);
   cases (true_or_false (f a)) #Hfa >Hfa normalize in ⊢ (%→?);
   #H destruct
   [% [@(ex_intro … []) % normalize [% % | #x #H destruct]
      |#a1 #tl1 #H destruct (H) //]
   |cases (Hind (a::acc) res1 res2 H) * #l1 * *
    #Hres1 #Htl #Hfalse #Htrue % [2:@Htrue] @(ex_intro … (l1@[a])) % 
     [% [>associative_append @Hres1 | >reverse_append <Htl % ]
     |#x #Hmemx cases (memb_append ???? Hmemx) 
        [@Hfalse | #H >(memb_single … H) //] 
     ]
   ]
  ]
qed.

axiom mem_reverse: ∀A,l,x. mem A x (reverse ? l) → mem A x l.

lemma split_on_spec_ex: ∀A:DeqSet.∀l,f.∃l1,l2.
    l1@l2 = l ∧ (∀x:A. memb ? x l1 = true → f x = false) ∧ 
    ∀a,tl. l2 = a::tl → f a = true.
#A #l #f @(ex_intro … (reverse … (\fst (split_on A l f [])))) 
@(ex_intro … (\snd (split_on A l f []))) 
cases (split_on_spec A l f [ ] ?? (eq_pair_fst_snd …)) * #l1 * *
>append_nil #Hl1 >Hl1 #Hl #Hfalse #Htrue % 
  [% [@Hl|#x #memx @Hfalse <(reverse_reverse … l1) @memb_reverse //] | @Htrue]
qed.

(* versione esistenziale *)

definition R_comp_step_true ≝ λt1,t2.
  ∃ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls 〈c,true〉 rs ∧
    ((* bit_or_null c = false *)
    (bit_or_null c = false → t2 = midtape ? ls 〈c,false〉 rs) ∧
    (* no marks in rs *)
    (bit_or_null c = true →
      (∀c.memb ? c rs = true → is_marked ? c = false) →
       ∀a,l. (a::l) = reverse ? (〈c,true〉::rs) → 
       t2 = rightof (FinProd FSUnialpha FinBool) a (l@ls)) ∧
    (∀l1,c0,l2.
      bit_or_null c = true →
      (∀c.memb ? c l1 = true → is_marked ? c = false) → 
      rs = l1@〈c0,true〉::l2 → 
      (c = c0 → 
       l2 = [ ] → (* test true but l2 is empty *) 
       t2 = rightof ? 〈c0,false〉 ((reverse ? l1)@〈c,true〉::ls))  ∧
      (c = c0 →
       ∀a,a0,b,l1',l2'. (* test true and l2 is not empty *) 
       〈a,false〉::l1' = l1@[〈c0,false〉] →
       l2 = 〈a0,b〉::l2' →
       t2 = midtape ? (〈c,false〉::ls) 〈a,true〉 (l1'@〈a0,true〉::l2')) ∧
      (c ≠ c0 →(* test false *)
       t2 = midtape (FinProd … FSUnialpha FinBool) 
         ((reverse ? l1)@〈c,true〉::ls) 〈c0,false〉 l2))).

definition R_comp_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   is_marked ? c = false ∧ t2 = t1.

lemma is_marked_to_exists: ∀alpha,c. is_marked alpha c = true →
 ∃c'. c = 〈c',true〉.
#alpha * #c * [#_ @(ex_intro … c) //| normalize #H destruct]
qed.

lemma exists_current: ∀alpha,c,t. 
  current alpha t = Some alpha c → ∃ls,rs. t= midtape ? ls c rs. 
#alpha #c * 
  [whd in ⊢ (??%?→?); #H destruct
  |#a #l whd in ⊢ (??%?→?); #H destruct
  |#a #l whd in ⊢ (??%?→?); #H destruct
  |#ls #c1 #rs whd in ⊢ (??%?→?); #H destruct
   @(ex_intro … ls) @(ex_intro … rs) //
  ]
qed.
   
lemma sem_comp_step : 
  accRealize ? comp_step (inr … (inl … (inr … start_nop))) 
    R_comp_step_true R_comp_step_false.
@(acc_sem_if_app … (sem_test_char ? (is_marked ?))
        (sem_comp_step_subcase FSUnialpha 〈bit false,true〉 ??
          (sem_comp_step_subcase FSUnialpha 〈bit true,true〉 ?? 
            (sem_comp_step_subcase FSUnialpha 〈null,true〉 ?? 
              (sem_clear_mark …))))
        (sem_nop …) …)
[#intape #outape #ta #Hta #Htb cases Hta * #cm * #Hcur 
 cases (exists_current … Hcur) #ls * #rs #Hintape #cmark
 cases (is_marked_to_exists … cmark) #c #Hcm
 >Hintape >Hcm -Hintape -Hcm #Hta
 @(ex_intro … ls) @(ex_intro … c) @(ex_intro …rs) % [//] lapply Hta -Hta
 (* #ls #c #rs #Hintape whd in Hta;
 >Hintape in Hta; * #_ -Hintape  forse non serve *)
 cases (true_or_false (c==bit false)) #Hc
  [>(\P Hc) #Hta %
    [%[whd in ⊢ ((??%?)→?); #Hdes destruct
      |#Hc @(proj1 ?? (proj1 ?? (Htb … Hta) (refl …)))
      ]
    |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (Htb … Hta) (refl …)))
    ] 
  |cases (true_or_false (c==bit true)) #Hc1
    [>(\P Hc1) #Hta  
      cut (〈bit true, true〉 ≠ 〈bit false, true〉) [% #Hdes destruct] #Hneq %
      [%[whd in ⊢ ((??%?)→?); #Hdes destruct
        |#Hc @(proj1 … (proj1 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) (refl …)))
        ]
      |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (proj2 ?? (Htb … Hta) Hneq … Hta)(refl …)))
      ]
    |cases (true_or_false (c==null)) #Hc2
      [>(\P Hc2) #Hta  
        cut (〈null, true〉 ≠ 〈bit false, true〉) [% #Hdes destruct] #Hneq
        cut (〈null, true〉 ≠ 〈bit true, true〉) [% #Hdes destruct] #Hneq1 %
        [%[whd in ⊢ ((??%?)→?); #Hdes destruct
          |#Hc @(proj1 … (proj1 ?? (proj2 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) Hneq1 … Hta) (refl …)))
          ]
        |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (proj2 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) Hneq1 … Hta) (refl …)))
        ]
      |#Hta cut (bit_or_null c = false)
        [lapply Hc; lapply Hc1; lapply Hc2 -Hc -Hc1 -Hc2
         cases c normalize [* normalize /2/] /2/] #Hcut %
        [%[cases (Htb … Hta) #_ -Htb #Htb
           cases (Htb … Hta) [2: % #H destruct (H) normalize in Hc; destruct] #_ -Htb #Htb 
           cases (Htb … Hta) [2: % #H destruct (H) normalize in Hc1; destruct] #_ -Htb #Htb 
           lapply (Htb ?) [% #H destruct (H) normalize in Hc2; destruct] 
           * #_ #Houttape #_ @(Houttape … Hta)
          |>Hcut #H destruct 
          ]
        |#l1 #c0 #l2 >Hcut #H destruct 
        ]
      ]
    ]
  ]
|#intape #outape #ta #Hta #Htb #ls #c #rs #Hintape 
 >Hintape in Hta; whd in ⊢ (%→?); * #Hmark #Hta % [@Hmark //]
 whd in Htb; >Htb //
]
qed.

(* old universal version  

definition R_comp_step_true ≝ λt1,t2.
  ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls 〈c,true〉 rs → 
    (* bit_or_null c = false *)
    (bit_or_null c = false → t2 = midtape ? ls 〈c,false〉 rs) ∧
    (* no marks in rs *)
    (bit_or_null c = true →
      (∀c.memb ? c rs = true → is_marked ? c = false) →
       ∀a,l. (a::l) = reverse ? (〈c,true〉::rs) → 
       t2 = rightof (FinProd FSUnialpha FinBool) a (l@ls)) ∧
    (∀l1,c0,l2.
      bit_or_null c = true →
      (∀c.memb ? c l1 = true → is_marked ? c = false) → 
      rs = l1@〈c0,true〉::l2 → 
      (c = c0 → 
       l2 = [ ] → (* test true but l2 is empty *) 
       t2 = rightof ? 〈c0,false〉 ((reverse ? l1)@〈c,true〉::ls))  ∧
      (c = c0 →
       ∀a,a0,b,l1',l2'. (* test true and l2 is not empty *) 
       〈a,false〉::l1' = l1@[〈c0,false〉] →
       l2 = 〈a0,b〉::l2' →
       t2 = midtape ? (〈c,false〉::ls) 〈a,true〉 (l1'@〈a0,true〉::l2')) ∧
      (c ≠ c0 →(* test false *)
       t2 = midtape (FinProd … FSUnialpha FinBool) 
         ((reverse ? l1)@〈c,true〉::ls) 〈c0,false〉 l2)).

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
[#intape #outape #ta #Hta #Htb #ls #c #rs #Hintape whd in Hta;
 >Hintape in Hta; * #_ -Hintape (* forse non serve *)
 cases (true_or_false (c==bit false)) #Hc
  [>(\P Hc) #Hta %
    [%[whd in ⊢ ((??%?)→?); #Hdes destruct
      |#Hc @(proj1 ?? (proj1 ?? (Htb … Hta) (refl …)))
      ]
    |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (Htb … Hta) (refl …)))
    ] 
  |cases (true_or_false (c==bit true)) #Hc1
    [>(\P Hc1) #Hta  
      cut (〈bit true, true〉 ≠ 〈bit false, true〉) [% #Hdes destruct] #Hneq %
      [%[whd in ⊢ ((??%?)→?); #Hdes destruct
        |#Hc @(proj1 … (proj1 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) (refl …)))
        ]
      |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (proj2 ?? (Htb … Hta) Hneq … Hta)(refl …)))
      ]
    |cases (true_or_false (c==null)) #Hc2
      [>(\P Hc2) #Hta  
        cut (〈null, true〉 ≠ 〈bit false, true〉) [% #Hdes destruct] #Hneq
        cut (〈null, true〉 ≠ 〈bit true, true〉) [% #Hdes destruct] #Hneq1 %
        [%[whd in ⊢ ((??%?)→?); #Hdes destruct
          |#Hc @(proj1 … (proj1 ?? (proj2 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) Hneq1 … Hta) (refl …)))
          ]
        |#l1 #c0 #l2 #Hc @(proj2 ?? (proj1 ?? (proj2 ?? (proj2 ?? (Htb … Hta) Hneq … Hta) Hneq1 … Hta) (refl …)))
        ]
      |#Hta cut (bit_or_null c = false)
        [lapply Hc; lapply Hc1; lapply Hc2 -Hc -Hc1 -Hc2
         cases c normalize [* normalize /2/] /2/] #Hcut %
        [%[cases (Htb … Hta) #_ -Htb #Htb
           cases (Htb … Hta) [2: % #H destruct (H) normalize in Hc; destruct] #_ -Htb #Htb 
           cases (Htb … Hta) [2: % #H destruct (H) normalize in Hc1; destruct] #_ -Htb #Htb 
           lapply (Htb ?) [% #H destruct (H) normalize in Hc2; destruct] 
           * #_ #Houttape #_ @(Houttape … Hta)
          |>Hcut #H destruct 
          ]
        |#l1 #c0 #l2 >Hcut #H destruct 
        ]
      ]
    ]
  ]
|#intape #outape #ta #Hta #Htb #ls #c #rs #Hintape 
 >Hintape in Hta; whd in ⊢ (%→?); * #Hmark #Hta % [@Hmark //]
 whd in Htb; >Htb //
]
qed. *)
 
(*   
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
qed.*)

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
  
definition list_cases2: ∀A.∀P:list A →list A →Prop.∀l1,l2. |l1| = |l2| → 
P [ ] [ ] → (∀a1,a2:A.∀tl1,tl2. |tl1| = |tl2| → P (a1::tl1) (a2::tl2)) → P l1 l2.
#A #P #l1 #l2 #Hlen lapply Hlen @(list_ind2 … Hlen) //
#tl1 #tl2 #hd1 #hd2 #Hind normalize #HlenS #H1 #H2 @H2 //
qed.

definition R_compare :=
  λt1,t2.
  ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
  (∀c'.bit_or_null c' = false → c = 〈c',true〉 → t2 = midtape ? ls 〈c',false〉 rs) ∧
  (∀c'. c = 〈c',false〉 → t2 = t1) ∧
(* forse manca il caso no marks in rs *)
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
  whd in Hleft; #ls #c #rs #Htapea cases Hleft -Hleft
  #ls0 * #c' * #rs0 * >Htapea #Hdes destruct (Hdes) * * 
  cases (true_or_false (bit_or_null c')) #Hc'
  [2: #Htapeb lapply (Htapeb Hc') -Htapeb #Htapeb #_ #_ %
    [%[#c1 #Hc1 #Heqc destruct (Heqc) 
       cases (IH … Htapeb) * #_ #H #_ <Htapeb @(H … (refl…)) 
      |#c1 #Heqc destruct (Heqc) 
      ]
    |#b #b0 #bs #b0s #l1 #l2 #_ #_ #_ #_ #_ #_
     #Heq destruct (Heq) >Hc' #Hfalse @False_ind destruct (Hfalse)
    ]
  |#_ (* no marks in rs ??? *) #_ #Hleft %
    [ %
      [ #c'' #Hc'' #Heq destruct (Heq) >Hc'' in Hc'; #H destruct (H) 
      | #c0 #Hfalse destruct (Hfalse)
      ]
    |#b #b0 #bs #b0s #l1 #l2 #Hlen #Hbs1 #Hb0s1 #Hbs2 #Hb0s2 #Hl1
     #Heq destruct (Heq) #_ >append_cons; <associative_append #Hrs
     cases (Hleft …  Hc' … Hrs) -Hleft
      [2: #c1 #memc1 cases (memb_append … memc1) -memc1 #memc1
        [cases (memb_append … memc1) -memc1 #memc1
          [@Hbs2 @memc1 |>(memb_single … memc1) %]
        |@Hl1 @memc1
        ]
      |* (* manca il caso in cui dopo una parte uguale il 
            secondo nastro finisca ... ???? *)
       #_ cases (true_or_false (b==b0)) #eqbb0
        [2: #_ #Htapeb %2 lapply (Htapeb … (\Pf eqbb0)) -Htapeb #Htapeb
         cases (IH … Htapeb) * #_ #Hout #_
         @(ex_intro … []) @(ex_intro … b) @(ex_intro … b0) 
         @(ex_intro … bs) @(ex_intro … b0s) %
          [%[%[@(\Pf eqbb0) | %] | %] 
          |>(Hout … (refl …)) -Hout >Htapeb @eq_f3 [2,3:%]
           >reverse_append >reverse_append >associative_append 
           >associative_append %  
          ]
        |lapply Hbs1 lapply Hb0s1 lapply Hbs2 lapply Hb0s2 lapply Hrs 
         -Hbs1 -Hb0s1 -Hbs2 -Hb0s2 -Hrs 
         @(list_cases2 … Hlen)
          [#Hrs #_ #_ #_ #_ >associative_append >associative_append #Htapeb #_
           lapply (Htapeb … (\P eqbb0) … (refl …) (refl …)) -Htapeb #Htapeb
           cases (IH … Htapeb) -IH * #Hout #_ #_ %1 %
            [>(\P eqbb0) % 
            |>(Hout grid (refl …) (refl …)) @eq_f 
             normalize >associative_append %
            ]
          |* #a1 #ba1 * #a2 #ba2 #tl1 #tl2 #HlenS #Hrs #Hb0s2 #Hbs2 #Hb0s1 #Hbs1 
           cut (ba1 = false) [@(Hbs2 〈a1,ba1〉) @memb_hd] #Hba1 >Hba1
           >associative_append >associative_append #Htapeb #_
           lapply (Htapeb … (\P eqbb0) … (refl …) (refl …)) -Htapeb #Htapeb
           cases (IH … Htapeb) -IH * #_ #_
           cut (ba2=false) [@(Hb0s2 〈a2,ba2〉) @memb_hd] #Hba2 >Hba2  
           #IH cases(IH a1 a2 ?? (l1@[〈b0,false〉]) l2 HlenS ????? (refl …) ??)
            [3:#x #memx @Hbs1 @memb_cons @memx
            |4:#x #memx @Hb0s1 @memb_cons @memx
            |5:#x #memx @Hbs2 @memb_cons @memx
            |6:#x #memx @Hb0s2 @memb_cons @memx
            |7:#x #memx cases (memb_append …memx) -memx #memx
              [@Hl1 @memx | >(memb_single … memx) %]
            |8:@(Hbs1 〈a1,ba1〉) @memb_hd
            |9: >associative_append >associative_append %
            |-IH -Hbs1 -Hb0s1 -Hbs2 -Hrs *
             #Ha1a2 #Houtc %1 %
              [>(\P eqbb0) @eq_f destruct (Ha1a2) %
              |>Houtc @eq_f3 
                [>reverse_cons >associative_append %
                |%
                |>associative_append % 
                ]
              ]
            |-IH -Hbs1 -Hb0s1 -Hbs2 -Hrs *
             #la * #c' * #d' * #lb * #lc * * * 
             #Hcd #H1 #H2 #Houtc %2
             @(ex_intro … (〈b,false〉::la)) @(ex_intro … c') @(ex_intro … d') 
             @(ex_intro … lb) @(ex_intro … lc) %
              [%[%[@Hcd | >H1 %] |>(\P eqbb0) >Hba2 >H2 %]
              |>Houtc @eq_f3 
                [>(\P eqbb0) >reverse_append >reverse_cons 
                 >reverse_cons >associative_append >associative_append
                 >associative_append >associative_append %
                |%
                |%
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
]
qed.
              
lemma WF_cst_niltape:
  WF ? (inv ? R_comp_step_true) (niltape (FinProd FSUnialpha FinBool)).
@wf #t1 whd in ⊢ (%→?); * #ls * #c * #rs * #H destruct 
qed.

lemma WF_cst_rightof:
  ∀a,ls. WF ? (inv ? R_comp_step_true) (rightof (FinProd FSUnialpha FinBool) a ls).
#a #ls @wf #t1 whd in ⊢ (%→?); * #ls * #c * #rs * #H destruct 
qed.

lemma WF_cst_leftof:
  ∀a,ls. WF ? (inv ? R_comp_step_true) (leftof (FinProd FSUnialpha FinBool) a ls).
#a #ls @wf #t1 whd in ⊢ (%→?); * #ls * #c * #rs * #H destruct 
qed.

lemma WF_cst_midtape_false:
  ∀ls,c,rs. WF ? (inv ? R_comp_step_true) 
    (midtape (FinProd … FSUnialpha FinBool) ls 〈c,false〉 rs).
#ls #c #rs @wf #t1 whd in ⊢ (%→?); * #ls' * #c' * #rs' * #H destruct 
qed.

(* da spostare *)
lemma not_nil_to_exists:∀A.∀l: list A. l ≠ [ ] →
 ∃a,tl. a::tl = l.
 #A * [* #H @False_ind @H // | #a #tl #_ @(ex_intro … a) @(ex_intro … tl) //]
 qed.

axiom daemon : ∀P:Prop.P.

lemma terminate_compare: 
  ∀t. Terminate ? compare t.
#t @(terminate_while … sem_comp_step) [%]
cases t // #ls * #c * // 
#rs lapply ls; lapply c; -ls -c 
(* we cannot proceed by structural induction on the right tape, 
   since compare moves the marks! *)
elim rs 
  [#c #ls @wf #t1 whd in ⊢ (%→?); * #ls0 * #c0 * #rs0 * #Hmid destruct (Hmid)
   * * #H1 #H2 #_ cases (true_or_false (bit_or_null c0)) #Hc0
    [>(H2 Hc0 … (refl …)) // #x whd in ⊢ ((??%?)→?); #Hdes destruct  
    |>(H1 Hc0) //
    ]
  |#a #rs' #Hind #c #ls @wf #t1 whd in ⊢ (%→?); * #ls0 * #c0 * #rs0 * #Hmid destruct (Hmid) 
   * * #H1 #H2 #H3 cases (true_or_false (bit_or_null c0)) #Hc0
    [-H1 cases (split_on_spec_ex ? (a::rs') (is_marked ?)) #rs1 * #rs2
     cases rs2
      [(* no marks in right tape *)
       * * >append_nil #H >H -H #Hmarks #_
       cases (not_nil_to_exists ? (reverse (FSUnialpha×bool) (〈c0,true〉::a::rs')) ?)
        [2: % >reverse_cons #H cases (nil_to_nil  … H) #_ #H1 destruct]
       #a0 * #tl #H4 >(H2 Hc0 Hmarks a0 tl H4) // 
      |(* the first marked element is a0 *)
       * #a0 #a0b #rs3 * * #H4 #H5 #H6 lapply (H3 ? a0 rs3 … Hc0 H5 ?)
        [<H4 @eq_f @eq_f2 [@eq_f @(H6 〈a0,a0b〉 … (refl …)) | %]
        |cases (true_or_false (c0==a0)) #eqc0a0 (* comparing a0 with c0 *)
          [* * (* we check if we have elements at the right of a0 *) cases rs3
            [#Ht1 #_ #_ >(Ht1 (\P eqc0a0) (refl …)) //
            |(* a1 will be marked *)
             cases (not_nil_to_exists ? (rs1@[〈a0,false〉]) ?)
               [2: % #H cases (nil_to_nil  … H) #_ #H1 destruct]
             * #a2 #a2b * #tl2 #H7 * #a1 #a1b #rs4 #_ #Ht1 #_ 
             cut (a2b =false) [@daemon] #Ha2b >Ha2b in H7; #H7   
             >(Ht1 (\P eqc0a0) … H7 (refl …)) 
             cut (rs' = tl2@〈a1,true〉::rs4)
             cut (a0b=false) [@(H6 〈a0,a0b〉)
       
    |>(H1 Hc0) //
    ]
qed.

axiom sem_compare : Realize ? compare R_compare.
