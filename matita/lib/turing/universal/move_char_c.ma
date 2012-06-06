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


(* MOVE_CHAR (variant c) MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls x cs # rs
       ^
       H

Output:
  ls cs x # rs
        ^
        H

Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

include "turing/basic_machines.ma".
include "turing/if_machine.ma".

definition mcc_step ≝ λalpha:FinSet.λsep:alpha.
  ifTM alpha (test_char ? (λc.¬c==sep))
     (single_finalTM … (seq … (swap_r alpha sep) (move_r ?))) (nop ?) tc_true.

definition Rmcc_step_true ≝ 
  λalpha,sep,t1,t2.
   ∀a,b,ls,rs.  
    t1 = midtape alpha (a::ls) b rs → 
    b ≠ sep ∧
    t2 = mk_tape alpha (a::b::ls) (option_hd ? rs) (tail ? rs).

definition Rmcc_step_false ≝ 
  λalpha,sep,t1,t2.
    left ? t1 ≠ [] →  current alpha t1 ≠ None alpha → 
      current alpha t1 = Some alpha sep ∧ t2 = t1.
    
lemma sem_mcc_step :
  ∀alpha,sep.
  mcc_step alpha sep ⊨ 
    [inr … (inl … (inr … start_nop)): Rmcc_step_true alpha sep, Rmcc_step_false alpha sep].  
#alpha #sep 
  @(acc_sem_if_app … 
     (sem_test_char …) (sem_seq …(sem_swap_r …) (sem_move_r …)) (sem_nop …))
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
definition move_char_c ≝ 
  λalpha,sep.whileTM alpha (mcc_step alpha sep) (inr … (inl … (inr … start_nop))).

definition R_move_char_c ≝ 
  λalpha,sep,t1,t2.
    ∀b,a,ls,rs. t1 = midtape alpha (a::ls) b rs → 
    (b = sep → t2 = t1) ∧
    (∀rs1,rs2.rs = rs1@sep::rs2 → 
     b ≠ sep → memb ? sep rs1 = false → 
     t2 = midtape alpha (a::reverse ? rs1@b::ls) sep rs2).
    
lemma sem_move_char_c :
  ∀alpha,sep.
  WRealize alpha (move_char_c alpha sep) (R_move_char_c alpha sep).
#alpha #sep #inc #i #outc #Hloop
lapply (sem_while … (sem_mcc_step alpha sep) inc i outc Hloop) [%]
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

lemma terminate_move_char_c :
  ∀alpha,sep.∀t,b,a,ls,rs. t = midtape alpha (a::ls) b rs →  
  (b = sep ∨ memb ? sep rs = true) → Terminate alpha (move_char_c alpha sep) t.
#alpha #sep #t #b #a #ls #rs #Ht #Hsep
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

(* NO GOOD: we must stop if current = None too!!! *)

axiom ssem_move_char_c :
  ∀alpha,sep.
  Realize alpha (move_char_c alpha sep) (R_move_char_c alpha sep).
