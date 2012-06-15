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


(* MOVE_CHAR RIGHT MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls x cs # rs
       ^
Output:
  ls cs x # rs
        ^
Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

include "turing/basic_machines.ma".
include "turing/if_machine.ma".

definition mcr_step ≝ λalpha:FinSet.λsep:alpha.
  ifTM alpha (test_char ? (λc.¬c==sep))
     (single_finalTM … (swap_l alpha sep · move_r ?)) (nop ?) tc_true.

definition Rmcr_step_true ≝ 
  λalpha,sep,t1,t2.
   ∀a,b,ls,rs.  
    t1 = midtape alpha (a::ls) b rs → 
    b ≠ sep ∧
    t2 = mk_tape alpha (a::b::ls) (option_hd ? rs) (tail ? rs).

definition Rmcr_step_false ≝ 
  λalpha,sep,t1,t2.
    left ? t1 ≠ [] →  current alpha t1 ≠ None alpha → 
      current alpha t1 = Some alpha sep ∧ t2 = t1.
    
lemma sem_mcr_step :
  ∀alpha,sep.
  mcr_step alpha sep ⊨ 
    [inr … (inl … (inr … start_nop)): Rmcr_step_true alpha sep, Rmcr_step_false alpha sep].  
#alpha #sep 
  @(acc_sem_if_app … 
     (sem_test_char …) (sem_seq …(sem_swap_l …) (sem_move_r …)) (sem_nop …))
  [#intape #outtape #tapea whd in ⊢ (%→%→%);
   #Htapea * #tapeb * whd in ⊢ (%→%→?);
   #Htapeb #Houttape #a #b #ls #rs #Hintape
   >Hintape in Htapea; #Htapea cases (Htapea ? (refl …)) -Htapea
   #Hbsep #Htapea % [@(\Pf (injective_notb ? false Hbsep))]
   @Houttape @Htapeb //
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   cases (current alpha intape) 
    [#_ #_ #_ * #Hfalse @False_ind @Hfalse %
    |#c #H #Htapea #_ #_ cases (H c (refl …)) #csep #Hintape % //
     lapply (injective_notb ? true csep) -csep #csep >(\P csep) //
    ]
  ]
qed.

(* the move_char (variant c) machine *)
definition move_char_r ≝ 
  λalpha,sep.whileTM alpha (mcr_step alpha sep) (inr … (inl … (inr … start_nop))).

definition R_move_char_r ≝ 
  λalpha,sep,t1,t2.
    ∀b,a,ls,rs. t1 = midtape alpha (a::ls) b rs → 
    (b = sep → t2 = t1) ∧
    (∀rs1,rs2.rs = rs1@sep::rs2 → 
     b ≠ sep → memb ? sep rs1 = false → 
     t2 = midtape alpha (a::reverse ? rs1@b::ls) sep rs2).
    
lemma sem_move_char_r :
  ∀alpha,sep.
  WRealize alpha (move_char_r alpha sep) (R_move_char_r alpha sep).
#alpha #sep #inc #i #outc #Hloop
lapply (sem_while … (sem_mcr_step alpha sep) inc i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea whd in ⊢ (% → ?); #H1 #b #a #ls #rs #Htapea
  %
  [ #Hb >Htapea in H1; >Hb #H1 cases (H1 ??)
    [#_ #H2 >H2 % |*: % #H2 normalize in H2; destruct (H2)]
  | #rs1 #rs2 #Hrs #Hb #Hrs1 
    >Htapea in H1; #H1 cases (H1 ??)
    [#Hfalse @False_ind @(absurd ?? Hb) normalize in Hfalse; destruct %
    |*:% #H2 normalize in H2; destruct (H2) ]
  ]
| #tapea #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH whd in ⊢ (%→%); #IH
  #a0 #b0 #ls #rs #Htapea cases (Hstar1 … Htapea)
  #Ha0 #Htapeb %
  [ #Hfalse @False_ind @(absurd ?? Ha0) //
  | *
    [ #rs2 whd in ⊢ (???%→?); #Hrs #_ #_ (* normalize *)
      >Hrs in Htapeb; #Htapeb normalize in Htapeb;
      cases (IH … Htapeb) #Houtc #_ >Houtc normalize // 
    | #r0 #rs0 #rs2 #Hrs #_ #Hrs0
      cut (r0 ≠ sep ∧ memb … sep rs0 = false)
      [ %
         [ % #Hr0 >Hr0 in Hrs0; >memb_hd #Hfalse destruct
         | whd in Hrs0:(??%?); cases (sep==r0) in Hrs0; normalize #Hfalse
           [ destruct
           | @Hfalse ]
         ]
      ] *
      #Hr0 -Hrs0 #Hrs0 >Hrs in Htapeb;
      normalize in ⊢ (%→?); #Htapeb
      cases (IH … Htapeb) -IH #_ #IH 
      >reverse_cons >associative_append @IH //
    ]
  ]
qed.

lemma terminate_move_char_r :
  ∀alpha,sep.∀t,b,a,ls,rs. t = midtape alpha (a::ls) b rs →  
  (b = sep ∨ memb ? sep rs = true) → Terminate alpha (move_char_r alpha sep) t.
#alpha #sep #t #b #a #ls #rs #Ht #Hsep
@(terminate_while … (sem_mcr_step alpha sep))
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

(* NO GOOD: we must stop if current = None too!!! *)

axiom ssem_move_char_r :
  ∀alpha,sep.
  Realize alpha (move_char_r alpha sep) (R_move_char_r alpha sep).


(******************************* move_char_l **********************************)
(* MOVE_CHAR (left) MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # 
alla sua sinistra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls # cs x rs
        ^
Output:
  ls # x cs rs
       ^
Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

include "turing/basic_machines.ma".
include "turing/if_machine.ma".

definition mcl_step ≝ λalpha:FinSet.λsep:alpha.
  ifTM alpha (test_char ? (λc.¬c==sep))
     (single_finalTM … (swap_r alpha sep · move_l ?)) (nop ?) tc_true.
     
definition Rmcl_step_true ≝ 
  λalpha,sep,t1,t2.
   ∀a,b,ls,rs.  
    t1 = midtape alpha ls b (a::rs) → 
    b ≠ sep ∧
    t2 = mk_tape alpha (tail ? ls) (option_hd ? ls) (a::b::rs).

definition Rmcl_step_false ≝ 
  λalpha,sep,t1,t2.
    right ? t1 ≠ [] →  current alpha t1 ≠ None alpha → 
      current alpha t1 = Some alpha sep ∧ t2 = t1.

definition mcls_acc: ∀alpha:FinSet.∀sep:alpha.states ? (mcl_step alpha sep)
 ≝ λalpha,sep.inr … (inl … (inr … start_nop)).

lemma sem_mcl_step :
  ∀alpha,sep.
  mcl_step alpha sep ⊨ 
    [mcls_acc alpha sep: Rmcl_step_true alpha sep, Rmcl_step_false alpha sep].
#alpha #sep 
@(acc_sem_if_app … 
  (sem_test_char …) (sem_seq …(sem_swap_r …) (sem_move_l …)) (sem_nop …))
  [#intape #outtape #tapea whd in ⊢ (%→%→%);
   #Htapea * #tapeb * whd in ⊢ (%→%→?);
   #Htapeb #Houttape #a #b #ls #rs #Hintape
   >Hintape in Htapea; #Htapea cases (Htapea ? (refl …)) -Htapea
   #Hbsep #Htapea % [@(\Pf (injective_notb ? false Hbsep))]
   @Houttape @Htapeb //
  |#intape #outtape #tapea whd in ⊢ (%→%→%);
   cases (current alpha intape) 
    [#_ #_ #_ * #Hfalse @False_ind @Hfalse %
    |#c #H #Htapea #_ #_ cases (H c (refl …)) #csep #Hintape % //
     lapply (injective_notb ? true csep) -csep #csep >(\P csep) //
    ]
  ]
qed.
    
(* the move_char (variant left) machine *)
definition move_char_l ≝ 
  λalpha,sep.whileTM alpha (mcl_step alpha sep) (inr … (inl … (inr … start_nop))).

definition R_move_char_l ≝ 
  λalpha,sep,t1,t2.
    ∀b,a,ls,rs. t1 = midtape alpha ls b (a::rs) → 
    (b = sep → t2 = t1) ∧
    (∀ls1,ls2.ls = ls1@sep::ls2 → 
     b ≠ sep → memb ? sep ls1 = false → 
     t2 = midtape alpha ls2 sep (a::reverse ? ls1@b::rs)).
    
lemma sem_move_char_l :
  ∀alpha,sep.
  WRealize alpha (move_char_l alpha sep) (R_move_char_l alpha sep).
#alpha #sep #inc #i #outc #Hloop
lapply (sem_while … (sem_mcl_step alpha sep) inc i outc Hloop) [%]
-Hloop * #t1 * #Hstar @(star_ind_l ??????? Hstar)
[ #tapea whd in ⊢ (% → ?); #H1 #b #a #ls #rs #Htapea
  %
  [ #Hb >Htapea in H1; >Hb #H1 cases (H1 ??)
   [#_ #H2 >H2 % |*: % #H2 normalize in H2; destruct (H2) ]
  | #rs1 #rs2 #Hrs #Hb #Hrs1 
    >Htapea in H1; (* normalize in ⊢ (% → ?); *) #H1 cases (H1 ??)
    [ #Hfalse normalize in Hfalse; @False_ind @(absurd ?? Hb) destruct %
    |*:% normalize #H2 destruct (H2) ]
  ]
| #tapea #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH whd in ⊢ (%→%); #IH
  #a0 #b0 #ls #rs #Htapea cases (Hstar1 … Htapea)
  #Ha0 #Htapeb %
  [ #Hfalse @False_ind @(absurd ?? Ha0) //
  | *
    [ #ls2 whd in ⊢ (???%→?); #Hls #_ #_
      >Hls in Htapeb; #Htapeb normalize in Htapeb;
      cases (IH … Htapeb) #Houtc #_ >Houtc normalize // 
    | #l0 #ls0 #ls2 #Hls #_ #Hls0
      cut (l0 ≠ sep ∧ memb … sep ls0 = false)
      [ %
         [ % #Hl0 >Hl0 in Hls0; >memb_hd #Hfalse destruct
         | whd in Hls0:(??%?); cases (sep==l0) in Hls0; normalize #Hfalse
           [ destruct
           | @Hfalse ]
         ]
      ] *
      #Hl0 -Hls0 #Hls0 >Hls in Htapeb;
      normalize in ⊢ (%→?); #Htapeb
      cases (IH … Htapeb) -IH #_ #IH 
      >reverse_cons >associative_append @IH //
    ]
  ]
qed.

lemma terminate_move_char_l :
  ∀alpha,sep.∀t,b,a,ls,rs. t = midtape alpha ls b (a::rs) → 
  (b = sep ∨ memb ? sep ls = true) → Terminate alpha (move_char_l alpha sep) t.
#alpha #sep #t #b #a #ls #rs #Ht #Hsep
@(terminate_while … (sem_mcl_step alpha sep))
  [%
  |generalize in match Hsep; -Hsep
   generalize in match Ht; -Ht
   generalize in match rs; -rs
   generalize in match a; -a
   generalize in match b; -b
   generalize in match t; -t
   elim ls 
    [#t #b #a #rs #Ht #Hsep % #tinit 
     whd in ⊢ (%→?); #H @False_ind
     cases (H … Ht) #Hb #_ cases Hb #eqb @eqb 
     cases Hsep // whd in ⊢ ((??%?)→?); #abs destruct
    |#l0 #ls0 #Hind #t #b #a #rs #Ht #Hsep % #tinit
     whd in ⊢ (%→?); #H 
     cases (H … Ht) #Hbsep #Htinit
     @(Hind … Htinit) cases Hsep 
      [#Hb @False_ind /2/ | #Hmemb cases (orb_true_l … Hmemb)
        [#eqsep %1 >(\P eqsep) // | #H %2 //]
  ]
qed.

(* NO GOOD: we must stop if current = None too!!! 
lemma ssem_move_char_l :
  ∀alpha,sep.
  Realize alpha (move_char_l alpha sep) (R_move_char_l alpha sep).
#alpha #sep *
[ %{5} % [| % [whd in ⊢ (??%?);
 @WRealize_to_Realize // @terminate_move_char_l
*)

axiom ssem_move_char_l :
  ∀alpha,sep.
  Realize alpha (move_char_l alpha sep) (R_move_char_l alpha sep).
