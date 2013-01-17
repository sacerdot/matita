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

include "turing/multi_universal/moves.ma".
include "turing/if_multi.ma".
include "turing/inject.ma".
include "turing/basic_machines.ma".

definition copy_states ≝ initN 3.

definition copy0 : copy_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition copy1 : copy_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition copy2 : copy_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).


definition trans_copy_step ≝ 
 λsrc,dst.λsig:FinSet.λn.
 λp:copy_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth src ? a (None ?) with
   [ None ⇒ 〈copy2,null_action sig n〉
   | Some ai ⇒ match nth dst ? a (None ?) with 
     [ None ⇒ 〈copy2,null_action ? n〉
     | Some aj ⇒ 
         〈copy1,change_vec ? (S n) 
           (change_vec ? (S n) (null_action ? n) (〈None ?,R〉) src)
           (〈Some ? ai,R〉) dst〉
     ]
   ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈copy1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈copy2,null_action ? n〉 ] ].

definition copy_step ≝ 
  λsrc,dst,sig,n.
  mk_mTM sig n copy_states (trans_copy_step src dst sig n) 
    copy0 (λq.q == copy1 ∨ q == copy2).

definition R_copy_step_true ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ∃x,y.
   current ? (nth src ? int (niltape ?)) = Some ? x ∧
   current ? (nth dst ? int (niltape ?)) = Some ? y ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move_mono ? (nth src ? int (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? int (niltape ?)) 〈Some ? x, R〉) dst.

definition R_copy_step_false ≝ 
  λsrc,dst:nat.λsig,n.λint,outt: Vector (tape sig) (S n).
    (current ? (nth src ? int (niltape ?)) = None ? ∨
     current ? (nth dst ? int (niltape ?)) = None ?) ∧ outt = int.

lemma copy_q0_q2_null :
  ∀src,dst,sig,n,v.src < S n → dst < S n → 
  (nth src ? (current_chars ?? v) (None ?) = None ? ∨
   nth dst ? (current_chars ?? v) (None ?) = None ?) → 
  step sig n (copy_step src dst sig n) (mk_mconfig ??? copy0 v) 
  = mk_mconfig ??? copy2 v.
#src #dst #sig #n #v #Hi #Hj
whd in ⊢ (? → ??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (?→??%?);
* #Hcurrent
[ @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent %
  | whd in ⊢ (??(????(???%))?); >Hcurrent @tape_move_null_action ]
| @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent cases (nth src ?? (None sig)) //
  | whd in ⊢ (??(????(???%))?); >Hcurrent
    cases (nth src ?? (None sig)) [|#x] @tape_move_null_action ] ]
qed.

lemma copy_q0_q1 :
  ∀src,dst,sig,n,v,a,b.src ≠ dst → src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = Some ? a →
  nth dst ? (current_chars ?? v) (None ?) = Some ? b → 
  step sig n (copy_step src dst sig n) (mk_mconfig ??? copy0 v) =
    mk_mconfig ??? copy1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move_mono ? (nth src ? v (niltape ?)) 〈None ?, R〉) src)
            (tape_move_mono ? (nth dst ? v (niltape ?)) 〈Some ? a, R〉) dst).
#src #dst #sig #n #v #a #b #Heq #Hsrc #Hdst #Ha1 #Ha2
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???%)?); >(\b ?) //
| whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(????(???%))?); >(\b ?) //
  change with (change_vec ?????) in ⊢ (??(????%)?);
  <(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
  >tape_move_multi_def 
  >pmap_change >pmap_change <tape_move_multi_def
  >tape_move_null_action
  @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_copy_step :
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  copy_step src dst sig n ⊨ 
    [ copy1: R_copy_step_true src dst sig n, 
            R_copy_step_false src dst sig n ].
#src #dst #sig #n #Hneq #Hsrc #Hdst #int
lapply (refl ? (current ? (nth src ? int (niltape ?))))
cases (current ? (nth src ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcur_src %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >copy_q0_q2_null /2/ 
    | normalize in ⊢ (%→?); #H destruct (H) ]
  | #_ % // % // ] ]
| #a #Ha lapply (refl ? (current ? (nth dst ? int (niltape ?))))
  cases (current ? (nth dst ? int (niltape ?))) in ⊢ (???%→?);
  [ #Hcur_dst %{2} %
    [| % [ %
       [ whd in ⊢ (??%?); >copy_q0_q2_null /2/ 
       | normalize in ⊢ (%→?); #H destruct (H) ]
       | #_ % // %2 >Hcur_dst % ] ]
  | #b #Hb %{2} %
    [| % [ % 
      [whd in ⊢  (??%?);  >(copy_q0_q1 … a b Hneq Hsrc Hdst) //
      | #_ %{a} %{b} % // % //]
      | * #H @False_ind @H %
      ]
    ]
  ]
]
qed.

definition copy ≝ λsrc,dst,sig,n.
  whileTM … (copy_step src dst sig n) copy1.

definition R_copy ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ((current ? (nth src ? int (niltape ?)) = None ? ∨
    current ? (nth dst ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,x0,rs,ls0,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x rs →
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃rs01,rs02.rs0 = rs01@rs02 ∧ |rs01| = |rs| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs@x::ls) (None sig) []) src)
            (mk_tape sig (reverse sig rs@x::ls0) (option_hd sig rs02)
            (tail sig rs02)) dst) ∨
    (∃rs1,rs2.rs = rs1@rs2 ∧ |rs1| = |rs0| ∧
     outt = change_vec ?? 
            (change_vec ?? int  
              (mk_tape sig (reverse sig rs1@x::ls) (option_hd sig rs2)
            (tail sig rs2)) src)
            (mk_tape sig (reverse sig rs1@x::ls0) (None sig) []) dst)).

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
