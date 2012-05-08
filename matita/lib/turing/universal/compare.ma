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

lemma sem_adv_to_mark_r :
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
  ∀t. (* ∀b,a,ls,rs. t = midtape alpha (a::ls) b rs →  
    (b = sep ∨ memb ? sep rs = true) →  *)
  Terminate alpha (adv_to_mark_r alpha test) t.
#alpha #test #t
@(terminate_while … (sem_atmr_step alpha test))
  [ %
  | % #t1 whd in ⊢ (% → ?); * #ls * #c * #rs
    * * generalize in match c; generalize in match ls;
    -ls -c elim rs
    [ #ls #c #Ht #Hc #Ht1
      % >Ht1 #t2 * #ls0 * #c0 * #rs0 * *
      normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
    
        
     #Ht #Hc #t1
    elim t 
    [ % #a whd in ⊢ (% → ?);

 #sep #t #b #a #ls #rs #Ht #Hsep
@(terminate_while … (sem_mcc_step alpha sep))
  [%
  |generalize in match Hsep; -Hsep
   generalize in match Ht; -Ht
   generalize in match ls; -ls
   generalize in match a; -a
   generalize in match b; -b
   generalize in match t; -t
   elim rs 
    [#t #b #a #ls #Ht #Hsep % #tinit 
     whd in ⊢ (%→?); #H @False_ind
     cases (H … Ht) #Hb #_ cases Hb #eqb @eqb 
     cases Hsep // whd in ⊢ ((??%?)→?); #abs destruct
    |#r0 #rs0 #Hind #t #b #a #ls #Ht #Hsep % #tinit
     whd in ⊢ (%→?); #H 
     cases (H … Ht) #Hbsep #Htinit
     @(Hind … Htinit) cases Hsep 
      [#Hb @False_ind /2/ | #Hmemb cases (orb_true_l … Hmemb)
        [#eqsep %1 >(\P eqsep) // | #H %2 //]
  ]
qed.