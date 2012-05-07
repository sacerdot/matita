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

include "turing/while_machine.ma".

definition mcc_states : FinSet → FinSet ≝ λalpha:FinSet.FinProd (initN 5) alpha.

definition mcc_step ≝ 
 λalpha:FinSet.λsep:alpha.
 mk_TM alpha (mcc_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  match a with 
  [ None ⇒ 〈〈4,sep〉,None ?〉 
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* qinit *)
    match a' == sep with
    [ true ⇒ 〈〈4,sep〉,None ?〉
    | false ⇒ 〈〈1,a'〉,Some ? 〈a',L〉〉 ]
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *)
      〈〈2,a'〉,Some ? 〈b,R〉〉
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *)
        〈〈3,sep〉,Some ? 〈b,R〉〉
      | S q' ⇒ match q' with
        [ O ⇒ (* qacc *)
          〈〈3,sep〉,None ?〉
        | S q' ⇒ (* qfail *)
          〈〈4,sep〉,None ?〉 ] ] ] ] ])
  〈0,sep〉
  (λq.let 〈q',a〉 ≝ q in q' == 3 ∨ q' == 4).

lemma mcc_q0_q1 : 
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  a0 == sep = false → 
  step alpha (mcc_step alpha sep)
    (mk_config ?? 〈0,a〉 (mk_tape … ls (Some ? a0) rs)) =
  mk_config alpha (states ? (mcc_step alpha sep)) 〈1,a0〉
    (tape_move_left alpha ls a0 rs).
#alpha #sep #a *
[ #a0 #rs #Ha0 whd in ⊢ (??%?); 
  normalize in match (trans ???); >Ha0 %
| #a1 #ls #a0 #rs #Ha0 whd in ⊢ (??%?);
  normalize in match (trans ???); >Ha0 %
]
qed.
    
lemma mcc_q1_q2 :
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  step alpha (mcc_step alpha sep) 
    (mk_config ?? 〈1,a〉 (mk_tape … ls (Some ? a0) rs)) = 
  mk_config alpha (states ? (mcc_step alpha sep)) 〈2,a0〉 
    (tape_move_right alpha ls a rs).
#alpha #sep #a #ls #a0 * //
qed.

lemma mcc_q2_q3 :
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  step alpha (mcc_step alpha sep) 
    (mk_config ?? 〈2,a〉 (mk_tape … ls (Some ? a0) rs)) = 
  mk_config alpha (states ? (mcc_step alpha sep)) 〈3,sep〉 
    (tape_move_right alpha ls a rs).
#alpha #sep #a #ls #a0 * //
qed.

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
    
lemma mcc_trans_init_sep: 
  ∀alpha,sep,x.
  trans ? (mcc_step alpha sep) 〈〈0,x〉,Some ? sep〉 = 〈〈4,sep〉,None ?〉.
#alpha #sep #x normalize >(\b ?) //
qed.
 
lemma mcc_trans_init_not_sep: 
  ∀alpha,sep,x,y.y == sep = false → 
  trans ? (mcc_step alpha sep) 〈〈0,x〉,Some ? y〉 = 〈〈1,y〉,Some ? 〈y,L〉〉.
#alpha #sep #x #y #H1 normalize >H1 //
qed.

lemma sem_mcc_step :
  ∀alpha,sep.
  accRealize alpha (mcc_step alpha sep) 
    〈3,sep〉 (Rmcc_step_true alpha sep) (Rmcc_step_false alpha sep).
#alpha #sep *
[@(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈4,sep〉 (niltape ?)))
  % [% [whd in ⊢ (??%?);% |#Hfalse destruct ] |#H1 #H2 @False_ind @(absurd ?? H2) %]
|#l0 #lt0 @(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈4,sep〉 (leftof ? l0 lt0)))
  % [% [whd in ⊢ (??%?);% |#Hfalse destruct ] |#H1 #H2 @False_ind @(absurd ?? H2) %]
|#r0 #rt0 @(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈4,sep〉 (rightof ? r0 rt0)))
  % [% [whd in ⊢ (??%?);% |#Hfalse destruct ] |#H1 #H2 #H3 @False_ind @(absurd ?? H3) %]
| #lt #c #rt cases (true_or_false (c == sep)) #Hc
  [ @(ex_intro ?? 2) 
    @(ex_intro ?? (mk_config ?? 〈4,sep〉 (midtape ? lt c rt)))
    % [ % 
        [ >(\P Hc) >loop_S_false // >loop_S_true 
         [ @eq_f whd in ⊢ (??%?); >mcc_trans_init_sep %
         |>(\P Hc) whd in ⊢(??(???(???%))?); >mcc_trans_init_sep % ]
        |   #Hfalse destruct ]
      |#_ #H1 #H2 % // normalize >(\P Hc) % ]
  | @(ex_intro ?? 4) cases lt
    [ @ex_intro
      [|% [ %
            [ >loop_S_false // >mcc_q0_q1 //
            | normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
          | normalize in ⊢ (%→?); #_ #H1 @False_ind @(absurd ?? H1) % ] ]
    | #l0 #lt @ex_intro
      [| % [ %
             [ >loop_S_false // >mcc_q0_q1 //
             | #_ #a #b #ls #rs #Hb destruct % 
               [ @(\Pf Hc)
               | >mcc_q1_q2 >mcc_q2_q3 cases rs normalize // ] ]
           | normalize in ⊢ (% → ?); * #Hfalse
             @False_ind /2/ ]
     ]
   ]
 ]
]
qed.

(* the move_char (variant c) machine *)
definition move_char_c ≝ 
  λalpha,sep.whileTM alpha (mcc_step alpha sep) 〈3,sep〉.

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
  [ #Hb >Htapea in H1; >Hb normalize in ⊢ (%→?); #H1
   cases (H1 ??)
   [#_ #H2 >H2 %
   |*: % #H2 destruct (H2) ]
  | #rs1 #rs2 #Hrs #Hb #Hrs1 
    >Htapea in H1; normalize in ⊢ (% → ?); #H1
    cases (H1 ??)
    [ #Hfalse @False_ind @(absurd ?? Hb) destruct %
    |*:% #H2 destruct (H2) ]
  ]
| #tapea #tapeb #tapec #Hstar1 #HRtrue #IH #HRfalse
  lapply (IH HRfalse) -IH whd in ⊢ (%→%); #IH
  #a0 #b0 #ls #rs #Htapea cases (Hstar1 … Htapea)
  #Ha0 #Htapeb %
  [ #Hfalse @False_ind @(absurd ?? Ha0) //
  | *
    [ #rs2 whd in ⊢ (???%→?); #Hrs #_ #_ normalize
      >Hrs in Htapeb; normalize #Htapeb
      cases (IH … Htapeb)
      #Houtc #_ >Houtc //
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