(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "turing/multi_universal/moves.ma".
include "turing/if_multi.ma".
include "turing/inject.ma".
include "turing/basic_machines.ma".

definition compare_states ≝ initN 3.

definition comp0 : compare_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition comp1 : compare_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition comp2 : compare_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

(*

0) (x,x) → (x,x)(R,R) → 1
   (x,y≠x) → None 2
1) (_,_) → None 1
2) (_,_) → None 2

*)

definition trans_compare_step ≝ 
 λi,j.λsig:FinSet.λn.
 λp:compare_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth i ? a (None ?) with
   [ None ⇒ 〈comp2,null_action ? n〉
   | Some ai ⇒ match nth j ? a (None ?) with 
     [ None ⇒ 〈comp2,null_action ? n〉
     | Some aj ⇒ if ai == aj 
         then 〈comp1,change_vec ? (S n) 
                      (change_vec ? (S n) (null_action ? n) (Some ? 〈ai,R〉) i)
                        (Some ? 〈aj,R〉) j〉
         else 〈comp2,null_action ? n〉 ]
   ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈comp1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈comp2,null_action ? n〉 ] ].

definition compare_step ≝ 
  λi,j,sig,n.
  mk_mTM sig n compare_states (trans_compare_step i j sig n) 
    comp0 (λq.q == comp1 ∨ q == comp2).

definition R_comp_step_true ≝ 
  λi,j,sig,n.λint,outt: Vector (tape sig) (S n).
  ∃x.
   current ? (nth i ? int (niltape ?)) = Some ? x ∧
   current ? (nth j ? int (niltape ?)) = Some ? x ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move ? (nth i ? int (niltape ?)) (Some ? 〈x,R〉)) i)
            (tape_move ? (nth j ? int (niltape ?)) (Some ? 〈x,R〉)) j.

definition R_comp_step_false ≝ 
  λi,j:nat.λsig,n.λint,outt: Vector (tape sig) (S n).
  (current ? (nth i ? int (niltape ?)) ≠ current ? (nth j ? int (niltape ?)) ∨
   current ? (nth i ? int (niltape ?)) = None ? ∨
   current ? (nth j ? int (niltape ?)) = None ?) ∧ outt = int.

lemma comp_q0_q2_null :
  ∀i,j,sig,n,v.i < S n → j < S n → 
  (nth i ? (current_chars ?? v) (None ?) = None ? ∨
   nth j ? (current_chars ?? v) (None ?) = None ?) → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #v #Hi #Hj
whd in ⊢ (? → ??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (?→??%?);
* #Hcurrent
[ @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent %
  | whd in ⊢ (??(???????(???%))?); >Hcurrent @tape_move_null_action ]
| @eq_f2
  [ whd in ⊢ (??(???%)?); >Hcurrent cases (nth i ?? (None sig)) //
  | whd in ⊢ (??(???????(???%))?); >Hcurrent
    cases (nth i ?? (None sig)) [|#x] @tape_move_null_action ] ]
qed.

lemma comp_q0_q2_neq :
  ∀i,j,sig,n,v.i < S n → j < S n → 
  nth i ? (current_chars ?? v) (None ?) ≠ nth j ? (current_chars ?? v) (None ?) → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #v #Hi #Hj lapply (refl ? (nth i ?(current_chars ?? v)(None ?)))
cases (nth i ?? (None ?)) in ⊢ (???%→?);
[ #Hnth #_ @comp_q0_q2_null // % //
| #ai #Hai lapply (refl ? (nth j ?(current_chars ?? v)(None ?)))
  cases (nth j ?? (None ?)) in ⊢ (???%→?);
  [ #Hnth #_ @comp_q0_q2_null // %2 //
  | #aj #Haj #Hneq
    whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
    [ whd in match (trans ????); >Hai >Haj
      whd in ⊢ (??(???%)?); >(\bf ?) // @(not_to_not … Hneq) //
    | whd in match (trans ????); >Hai >Haj
      whd in ⊢ (??(???????(???%))?); >(\bf ?) /2 by not_to_not/
      @tape_move_null_action
] ]
qed.

lemma comp_q0_q1 :
  ∀i,j,sig,n,v,a.i ≠ j → i < S n → j < S n → 
  nth i ? (current_chars ?? v) (None ?) = Some ? a →
  nth j ? (current_chars ?? v) (None ?) = Some ? a → 
  step sig n (compare_step i j sig n) (mk_mconfig ??? comp0 v) =
    mk_mconfig ??? comp1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? (nth i ? v (niltape ?)) (Some ? 〈a,R〉)) i)
       (tape_move ? (nth j ? v (niltape ?)) (Some ? 〈a,R〉)) j).
#i #j #sig #n #v #a #Heq #Hi #Hj #Ha1 #Ha2
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???%)?); >(\b ?) //
| whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???????(???%))?); >(\b ?) //
  change with (change_vec ?????) in ⊢ (??(???????%)?);
  <(change_vec_same … v j (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v i (niltape ?)) in ⊢ (??%?);
  >pmap_change >pmap_change >tape_move_null_action
  @eq_f2 // @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_comp_step :
  ∀i,j,sig,n.i ≠ j → i < S n → j < S n → 
  compare_step i j sig n ⊨ 
    [ comp1: R_comp_step_true i j sig n, 
             R_comp_step_false i j sig n ].
#i #j #sig #n #Hneq #Hi #Hj #int
lapply (refl ? (current ? (nth i ? int (niltape ?))))
cases (current ? (nth i ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcuri %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >comp_q0_q2_null /2/ % <Hcuri in ⊢ (???%); 
      @sym_eq @nth_vec_map
    | normalize in ⊢ (%→?); #H destruct (H) ]
  | #_ % // % %2 // ] ]
| #a #Ha lapply (refl ? (current ? (nth j ? int (niltape ?))))
  cases (current ? (nth j ? int (niltape ?))) in ⊢ (???%→?);
  [ #Hcurj %{2} %
    [| % [ %
       [ whd in ⊢ (??%?); >comp_q0_q2_null /2/ %2 <Hcurj in ⊢ (???%); 
         @sym_eq @nth_vec_map
       | normalize in ⊢ (%→?); #H destruct (H) ]
       | #_ % >Ha >Hcurj % % % #H destruct (H) ] ]
  | #b #Hb %{2} cases (true_or_false (a == b)) #Hab
    [ %
      [| % [ % 
        [whd in ⊢  (??%?);  >(comp_q0_q1 … a Hneq Hi Hj) //
          [>(\P Hab) <Hb @sym_eq @nth_vec_map
          |<Ha @sym_eq @nth_vec_map ]
        | #_ whd >(\P Hab) %{b} % // % // <(\P Hab) // ]
        | * #H @False_ind @H %
      ] ]
    | %
      [| % [ % 
        [whd in ⊢  (??%?);  >comp_q0_q2_neq //
         <(nth_vec_map ?? (current …) i ? int (niltape ?))
         <(nth_vec_map ?? (current …) j ? int (niltape ?)) >Ha >Hb
         @(not_to_not ??? (\Pf Hab)) #H destruct (H) %
        | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % // % % >Ha >Hb @(not_to_not ??? (\Pf Hab)) #H destruct (H) % ] ]
    ]
  ]
]
qed.

definition compare ≝ λi,j,sig,n.
  whileTM … (compare_step i j sig n) comp1.

definition R_compare ≝ 
  λi,j,sig,n.λint,outt: Vector (tape sig) (S n).
  (current sig (nth i (tape sig) int (niltape sig))
   ≠current sig (nth j (tape sig) int (niltape sig)) → 
   outt = int) ∧  
  (∀ls,x,xs,ci,rs,ls0,cj,rs0. 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x (xs@cj::rs0) → ci ≠ cj → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (midtape sig (reverse ? xs@x::ls0) cj rs0) j).

lemma wsem_compare : ∀i,j,sig,n.i ≠ j → i < S n → j < S n → 
  compare i j sig n ⊫ R_compare i j sig n.
#i #j #sig #n #Hneq #Hi #Hj #ta #k #outc #Hloop
lapply (sem_while … (sem_comp_step i j sig n Hneq Hi Hj) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * * [ *
  [ #Hcicj #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hnthi #Hnthj
      >Hnthi in Hcicj; >Hnthj normalize in ⊢ (%→?); * #H @False_ind @H %
    ]
  | #Hci #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hnthi >Hnthi in Hci;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #Hcj #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #Hnthj >Hnthj in Hcj;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #tc #td #te * #x * * #Hci #Hcj #Hd #Hstar #IH #He lapply (IH He) -IH *
    #IH1 #IH2 %
    [ >Hci >Hcj * #H @False_ind @H %
    | #ls #c0 #xs #ci #rs #ls0 #cj #rs0 cases xs
      [ #Hnthi #Hnthj #Hcicj >IH1 
        [ >Hd @eq_f3 // 
          [ @eq_f3 // >(?:c0=x) [ >Hnthi % ]
            >Hnthi in Hci;normalize #H destruct (H) %
          | >(?:c0=x) [ >Hnthj % ]
            >Hnthi in Hci;normalize #H destruct (H) % ]
        | >Hd >nth_change_vec // >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec // >Hnthi >Hnthj normalize @(not_to_not ??? Hcicj)
          #H destruct (H) % ]
      | #x0 #xs0 #Hnthi #Hnthj #Hcicj
        >(IH2 (c0::ls) x0 xs0 ci rs (c0::ls0) cj rs0 … Hcicj)
        [ >Hd >change_vec_commute in ⊢ (??%?); //
          >change_vec_change_vec >change_vec_commute in ⊢ (??%?); //
          @sym_not_eq //
        | >Hd >nth_change_vec // >Hnthj normalize
          >Hnthi in Hci;normalize #H destruct (H) %
        | >Hd >nth_change_vec_neq [|@sym_not_eq //] >Hnthi
          >nth_change_vec // normalize
          >Hnthi in Hci;normalize #H destruct (H) %
        ]
]]]
qed.      
 
lemma terminate_compare :  ∀i,j,sig,n,t.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n  ↓ t.
#i #j #sig #n #t #Hneq #Hi #Hj
@(terminate_while … (sem_comp_step …)) //
<(change_vec_same … t i (niltape ?))
cases (nth i (tape sig) t (niltape ?))
[ % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct 
|2,3: #a0 #al0 % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #Hxsep >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcur
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_compare : ∀i,j,sig,n.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n ⊨ R_compare i j sig n.
#i #j #sig #n #Hneq #Hi #Hj @WRealize_to_Realize /2/
qed.

(*
   |conf1   $
   |confin 0/1 confout move

  match machine step ≝
    compare;
    if (cur(src) != $)
      then
        parmoveL;
        moveR(dst);
      else nop
 *)

definition match_step ≝ λsrc,dst,sig,n,is_startc,is_endc.
  compare src dst sig n ·
    (ifTM ?? (inject_TM ? (test_char ? is_endc) n src) 
      (single_finalTM ??
        (parmove src dst sig n L is_startc · (inject_TM ? (move_r ?) n dst)))
      (nop ? n)
      tc_false).

definition R_match_step_false ≝ 
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
    ∃ls,ls0,rs,rs0,x,xs,end,c.
    is_endc end = true ∧
    nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) ∧
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@c::rs0) ∧
    outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
           (midtape sig (reverse ? xs@x::ls0) c rs0) dst.

(*
  src : | 
*)

definition R_match_step_true ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀s.current sig (nth src (tape sig) int (niltape sig)) = Some ? s → 
  is_startc s = true →
  (∀s1.current sig (nth dst (tape sig) int (niltape sig)) = Some ? s1 →
   s ≠ s1 →  
   outt = change_vec ?? int 
          (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈s1,R〉)) dst ∧ is_endc s = false) ∧  
  (∀ls,x,xs,ci,rs,ls0,cj,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@cj::rs0) → ci ≠ cj → 
    outt = change_vec ?? int 
           (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈x,R〉)) dst ∧ is_endc ci = false).

definition Rtc_multi_true ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
   (∃c. current alpha (nth i ? t1 (niltape ?)) = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_multi_false ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
    (∀c. current alpha (nth i ? t1 (niltape ?)) = Some ? c → test c = false) ∧ t2 = t1.
    
lemma sem_test_char_multi :
  ∀alpha,test,n,i.i ≤ n → 
  inject_TM ? (test_char ? test) n i ⊨ 
  [ tc_true : Rtc_multi_true alpha test n i, Rtc_multi_false alpha test n i ].
#alpha #test #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_char alpha test) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * * #c *
  #Hcur #Htestc #Hnth_i #Hnth_j %
  [ %{c} % //
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
| #Hqfalse lapply (Hfalse Hqfalse) * * #Htestc #Hnth_i #Hnth_j %
  [ @Htestc
  | @(eq_vec … (niltape ?)) #i0 #Hi0
    cases (decidable_eq_nat i0 i) #Hi0i
    [ >Hi0i @Hnth_i
    | @sym_eq @Hnth_j @sym_not_eq // ] ] ]
qed.

lemma sem_match_step :
  ∀src,dst,sig,n,is_startc,is_endc.src ≠ dst → src < S n → dst < S n → 
  match_step src dst sig n is_startc is_endc ⊨ 
    [ inr … (inr … (inr … start_nop)) : 
      R_match_step_true src dst sig n is_startc is_endc, 
      R_match_step_false src dst sig n is_endc ].
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst
@(acc_sem_seq_app … (sem_compare … Hneq Hsrc Hdst)
    (acc_sem_if … (sem_test_char_multi ? ()
      (sem_nop …)
        (sem_seq … sem_mark_next_tuple 
           (sem_if … (sem_test_char ? (λc:STape.is_grid (\fst c)))
             (sem_mark ?) (sem_seq … (sem_move_l …) (sem_init_current …))))))
  (sem_nop ?) …)

 #int
