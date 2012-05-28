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


(* MOVE_CHAR (left) MACHINE

Sposta il carattere binario su cui si trova la testina appena prima del primo # alla sua destra.

Input:
(ls,cs,rs can be empty; # is a parameter)

  ls # cs x rs
        ^
        H

Output:
  ls # x cs rs
       ^
       H

Initial state = 〈0,#〉
Final state = 〈4,#〉

*)

include "turing/while_machine.ma".

definition mcl_states : FinSet → FinSet ≝ λalpha:FinSet.FinProd (initN 5) alpha.

definition mcl0 : initN 5 ≝ mk_Sig ?? 0 (leb_true_to_le 1 5 (refl …)).
definition mcl1 : initN 5 ≝ mk_Sig ?? 1 (leb_true_to_le 2 5 (refl …)).
definition mcl2 : initN 5 ≝ mk_Sig ?? 2 (leb_true_to_le 3 5 (refl …)).
definition mcl3 : initN 5 ≝ mk_Sig ?? 3 (leb_true_to_le 4 5 (refl …)).
definition mcl4 : initN 5 ≝ mk_Sig ?? 4 (leb_true_to_le 5 5 (refl …)).

definition mcl_step ≝ 
 λalpha:FinSet.λsep:alpha.
 mk_TM alpha (mcl_states alpha)
 (λp.let 〈q,a〉 ≝ p in
  let 〈q',b〉 ≝ q in
  let q' ≝ pi1 nat (λi.i<5) q' in (* perche' devo passare il predicato ??? *)
  match a with 
  [ None ⇒ 〈〈mcl4,sep〉,None ?〉 
  | Some a' ⇒ 
  match q' with
  [ O ⇒ (* qinit *)
    match a' == sep with
    [ true ⇒ 〈〈mcl4,sep〉,None ?〉
    | false ⇒ 〈〈mcl1,a'〉,Some ? 〈a',R〉〉 ]
  | S q' ⇒ match q' with
    [ O ⇒ (* q1 *)
      〈〈mcl2,a'〉,Some ? 〈b,L〉〉
    | S q' ⇒ match q' with
      [ O ⇒ (* q2 *)
        〈〈mcl3,sep〉,Some ? 〈b,L〉〉
      | S q' ⇒ match q' with
        [ O ⇒ (* qacc *)
          〈〈mcl3,sep〉,None ?〉
        | S q' ⇒ (* qfail *)
          〈〈mcl4,sep〉,None ?〉 ] ] ] ] ])
  〈mcl0,sep〉
  (λq.let 〈q',a〉 ≝ q in q' == mcl3 ∨ q' == mcl4).

lemma mcl_q0_q1 : 
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  a0 == sep = false → 
  step alpha (mcl_step alpha sep)
    (mk_config ?? 〈mcl0,a〉 (mk_tape … ls (Some ? a0) rs)) =
  mk_config alpha (states ? (mcl_step alpha sep)) 〈mcl1,a0〉
    (tape_move_right alpha ls a0 rs).
#alpha #sep #a *
[ #a0 #rs #Ha0 whd in ⊢ (??%?); 
  normalize in match (trans ???); >Ha0 %
| #a1 #ls #a0 #rs #Ha0 whd in ⊢ (??%?);
  normalize in match (trans ???); >Ha0 %
]
qed.
    
lemma mcl_q1_q2 :
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  step alpha (mcl_step alpha sep) 
    (mk_config ?? 〈mcl1,a〉 (mk_tape … ls (Some ? a0) rs)) = 
  mk_config alpha (states ? (mcl_step alpha sep)) 〈mcl2,a0〉 
    (tape_move_left alpha ls a rs).
#alpha #sep #a #ls #a0 * //
qed.

lemma mcl_q2_q3 :
  ∀alpha:FinSet.∀sep,a,ls,a0,rs.
  step alpha (mcl_step alpha sep) 
    (mk_config ?? 〈mcl2,a〉 (mk_tape … ls (Some ? a0) rs)) = 
  mk_config alpha (states ? (mcl_step alpha sep)) 〈mcl3,sep〉 
    (tape_move_left alpha ls a rs).
#alpha #sep #a #ls #a0 * //
qed.

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
    
lemma mcl_trans_init_sep: 
  ∀alpha,sep,x.
  trans ? (mcl_step alpha sep) 〈〈mcl0,x〉,Some ? sep〉 = 〈〈mcl4,sep〉,None ?〉.
#alpha #sep #x normalize >(\b ?) //
qed.
 
lemma mcl_trans_init_not_sep: 
  ∀alpha,sep,x,y.y == sep = false → 
  trans ? (mcl_step alpha sep) 〈〈mcl0,x〉,Some ? y〉 = 〈〈mcl1,y〉,Some ? 〈y,R〉〉.
#alpha #sep #x #y #H1 normalize >H1 //
qed.

lemma sem_mcl_step :
  ∀alpha,sep.
  accRealize alpha (mcl_step alpha sep) 
    〈mcl3,sep〉 (Rmcl_step_true alpha sep) (Rmcl_step_false alpha sep).
#alpha #sep cut (∀P:Prop.〈mcl4,sep〉=〈mcl3,sep〉→P)
  [#P whd in ⊢ ((??(???%?)(???%?))→?); #Hfalse destruct] #Hfalse
*
[@(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈mcl4,sep〉 (niltape ?)))
  % [% [whd in ⊢ (??%?);% |@Hfalse] |#H1 #H2 @False_ind @(absurd ?? H2) %]
|#l0 #lt0 @(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈mcl4,sep〉 (leftof ? l0 lt0)))
  % [% [whd in ⊢ (??%?);% |@Hfalse] |#H1 #H2 #H3 @False_ind @(absurd ?? H3) %]
|#r0 #rt0 @(ex_intro ?? 2)  
  @(ex_intro … (mk_config ?? 〈mcl4,sep〉 (rightof ? r0 rt0)))
  % [% [whd in ⊢ (??%?);% |@Hfalse] |#H1 #H2 #H3 @False_ind @(absurd ?? H3) %]
| #lt #c #rt cases (true_or_false (c == sep)) #Hc
  [ @(ex_intro ?? 2) 
    @(ex_intro ?? (mk_config ?? 〈mcl4,sep〉 (midtape ? lt c rt)))
    % [ % 
        [ >(\P Hc) >loop_S_false // >loop_S_true 
          [ @eq_f whd in ⊢ (??%?); >mcl_trans_init_sep %
          |>(\P Hc) whd in ⊢(??(???(???%))?); >mcl_trans_init_sep % ]
        |@Hfalse]
      |#_ #H1 #H2 % // normalize >(\P Hc) % ]
  |@(ex_intro ?? 4) cases rt
    [ @ex_intro
      [|% [ %
            [ >loop_S_false // >mcl_q0_q1 //
            | normalize in ⊢ (%→?); @Hfalse]
          | normalize in ⊢ (%→?); #_ #H1 @False_ind @(absurd ?? H1) % ] ]
   | #r0 #rt0 @ex_intro
      [| % [ %
             [ >loop_S_false // >mcl_q0_q1 //
             | #_ #a #b #ls #rs #Hb destruct (Hb) % 
               [ @(\Pf Hc)
               | >mcl_q1_q2 >mcl_q2_q3 cases ls normalize // ] ]
           | normalize in ⊢ (% → ?); * #Hfalse
             @False_ind /2/ ]
     ]
   ]
 ]
]
qed.

(* the move_char (variant c) machine *)
definition move_char_l ≝ 
  λalpha,sep.whileTM alpha (mcl_step alpha sep) 〈mcl3,sep〉.

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