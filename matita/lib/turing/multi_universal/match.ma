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
 λi,j.λsig:FinSet.λn.λis_endc.
 λp:compare_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth i ? a (None ?) with
   [ None ⇒ 〈comp2,null_action ? n〉
   | Some ai ⇒ match nth j ? a (None ?) with 
     [ None ⇒ 〈comp2,null_action ? n〉
     | Some aj ⇒ if notb (is_endc ai) ∧ ai == aj 
         then 〈comp1,change_vec ? (S n) 
                      (change_vec ? (S n) (null_action ? n) (Some ? 〈ai,R〉) i)
                        (Some ? 〈aj,R〉) j〉
         else 〈comp2,null_action ? n〉 ]
   ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈comp1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈comp2,null_action ? n〉 ] ].

definition compare_step ≝ 
  λi,j,sig,n,is_endc.
  mk_mTM sig n compare_states (trans_compare_step i j sig n is_endc) 
    comp0 (λq.q == comp1 ∨ q == comp2).

definition R_comp_step_true ≝ 
  λi,j,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
  ∃x.
   is_endc x = false ∧
   current ? (nth i ? int (niltape ?)) = Some ? x ∧
   current ? (nth j ? int (niltape ?)) = Some ? x ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move ? (nth i ? int (niltape ?)) (Some ? 〈x,R〉)) i)
            (tape_move ? (nth j ? int (niltape ?)) (Some ? 〈x,R〉)) j.

definition R_comp_step_false ≝ 
  λi,j:nat.λsig,n,is_endc.λint,outt: Vector (tape sig) (S n).
   ((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
   current ? (nth i ? int (niltape ?)) ≠ current ? (nth j ? int (niltape ?)) ∨
   current ? (nth i ? int (niltape ?)) = None ? ∨
   current ? (nth j ? int (niltape ?)) = None ?) ∧ outt = int.

lemma comp_q0_q2_null :
  ∀i,j,sig,n,is_endc,v.i < S n → j < S n → 
  (nth i ? (current_chars ?? v) (None ?) = None ? ∨
   nth j ? (current_chars ?? v) (None ?) = None ?) → 
  step sig n (compare_step i j sig n is_endc) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #is_endc #v #Hi #Hj
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
  ∀i,j,sig,n,is_endc,v.i < S n → j < S n → 
  ((∃x.nth i ? (current_chars ?? v) (None ?) = Some ? x ∧ is_endc x = true) ∨ 
    nth i ? (current_chars ?? v) (None ?) ≠ nth j ? (current_chars ?? v) (None ?)) → 
  step sig n (compare_step i j sig n is_endc) (mk_mconfig ??? comp0 v) 
  = mk_mconfig ??? comp2 v.
#i #j #sig #n #is_endc #v #Hi #Hj lapply (refl ? (nth i ?(current_chars ?? v)(None ?)))
cases (nth i ?? (None ?)) in ⊢ (???%→?);
[ #Hnth #_ @comp_q0_q2_null // % //
| #ai #Hai lapply (refl ? (nth j ?(current_chars ?? v)(None ?)))
  cases (nth j ?? (None ?)) in ⊢ (???%→?);
  [ #Hnth #_ @comp_q0_q2_null // %2 //
  | #aj #Haj *
    [ * #c * >Hai #Heq #Hendc whd in ⊢ (??%?); 
      >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
      [ whd in match (trans ????); >Hai >Haj destruct (Heq) 
        whd in ⊢ (??(???%)?); >Hendc // 
      | whd in match (trans ????); >Hai >Haj destruct (Heq) 
        whd in ⊢ (??(???????(???%))?); >Hendc @tape_move_null_action
      ]
    | #Hneq
      whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
      [ whd in match (trans ????); >Hai >Haj
        whd in ⊢ (??(???%)?); cut ((¬is_endc ai∧ai==aj)=false)
        [>(\bf ?) /2 by not_to_not/ cases (is_endc ai) // |#Hcut >Hcut //]
        | whd in match (trans ????); >Hai >Haj
          whd in ⊢ (??(???????(???%))?); cut ((¬is_endc ai∧ai==aj)=false)
          [>(\bf ?) /2 by not_to_not/ cases (is_endc ai) // 
          |#Hcut >Hcut @tape_move_null_action
          ]
        ]
      ]
    ]
]
qed.

lemma comp_q0_q1 :
  ∀i,j,sig,n,is_endc,v,a.i ≠ j → i < S n → j < S n → 
  nth i ? (current_chars ?? v) (None ?) = Some ? a → is_endc a = false →
  nth j ? (current_chars ?? v) (None ?) = Some ? a → 
  step sig n (compare_step i j sig n is_endc) (mk_mconfig ??? comp0 v) =
    mk_mconfig ??? comp1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? (nth i ? v (niltape ?)) (Some ? 〈a,R〉)) i)
       (tape_move ? (nth j ? v (niltape ?)) (Some ? 〈a,R〉)) j).
#i #j #sig #n #is_endc #v #a #Heq #Hi #Hj #Ha1 #Hnotendc #Ha2
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???%)?); >Hnotendc >(\b ?) //
| whd in match (trans ????);
  >Ha1 >Ha2 whd in ⊢ (??(???????(???%))?); >Hnotendc >(\b ?) //
  change with (change_vec ?????) in ⊢ (??(???????%)?);
  <(change_vec_same … v j (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v i (niltape ?)) in ⊢ (??%?);
  >pmap_change >pmap_change >tape_move_null_action
  @eq_f2 // @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_comp_step :
  ∀i,j,sig,n,is_endc.i ≠ j → i < S n → j < S n → 
  compare_step i j sig n is_endc ⊨ 
    [ comp1: R_comp_step_true i j sig n is_endc, 
             R_comp_step_false i j sig n is_endc ].
#i #j #sig #n #is_endc #Hneq #Hi #Hj #int
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
       | #_ % // >Ha >Hcurj % % %2 % #H destruct (H) ] ]
  | #b #Hb %{2} 
   cases (true_or_false (is_endc a)) #Haendc
    [ %
      [| % [ % 
        [whd in ⊢  (??%?);  >comp_q0_q2_neq //
         % %{a} % // <Ha @sym_eq @nth_vec_map
        | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % // % % % >Ha %{a} % // ]
      ]
    |cases (true_or_false (a == b)) #Hab
      [ %
        [| % [ % 
          [whd in ⊢  (??%?);  >(comp_q0_q1 … a Hneq Hi Hj) //
            [>(\P Hab) <Hb @sym_eq @nth_vec_map
            |<Ha @sym_eq @nth_vec_map ]
          | #_ whd >(\P Hab) %{b} % // % // <(\P Hab) % // ]
          | * #H @False_ind @H %
        ] ]
      | %
        [| % [ % 
          [whd in ⊢  (??%?);  >comp_q0_q2_neq //
           <(nth_vec_map ?? (current …) i ? int (niltape ?))
           <(nth_vec_map ?? (current …) j ? int (niltape ?)) %2 >Ha >Hb
           @(not_to_not ??? (\Pf Hab)) #H destruct (H) %
          | normalize in ⊢ (%→?); #H destruct (H) ]
        | #_ % // % % %2 >Ha >Hb @(not_to_not ??? (\Pf Hab)) #H destruct (H) % ] ]
      ]
    ]
  ]
]
qed.

definition compare ≝ λi,j,sig,n,is_endc.
  whileTM … (compare_step i j sig n is_endc) comp1.

definition R_compare ≝ 
  λi,j,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
  ((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
   (current ? (nth i ? int (niltape ?)) ≠ current ? (nth j ? int (niltape ?)) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,xs,ci,rs,ls0,rs0. 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x (xs@rs0) →
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → 
    (rs0 = [ ] ∧
     outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (mk_tape sig (reverse ? xs@x::ls0) (None ?) []) j) ∨
    ∃cj,rs1.rs0 = cj::rs1 ∧
    ((is_endc ci = true ∨ ci ≠ cj) → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (midtape sig (reverse ? xs@x::ls0) cj rs1) j)).
          
lemma wsem_compare : ∀i,j,sig,n,is_endc.i ≠ j → i < S n → j < S n → 
  compare i j sig n is_endc ⊫ R_compare i j sig n is_endc.
#i #j #sig #n #is_endc #Hneq #Hi #Hj #ta #k #outc #Hloop
lapply (sem_while … (sem_comp_step i j sig n is_endc Hneq Hi Hj) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * * [ * [ *
  [* #curi * #Hcuri #Hendi #Houtc %
    [ #_ @Houtc  
    | #ls #x #xs #ci #rs #ls0 #rs0 #Hnthi #Hnthj #Hnotendc 
      @False_ind
      >Hnthi in Hcuri; normalize in ⊢ (%→?); #H destruct (H)
      >(Hnotendc ? (memb_hd … )) in Hendi; #H destruct (H)
    ]
  |#Hcicj #Houtc % 
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #rs0 #Hnthi #Hnthj
      >Hnthi in Hcicj; >Hnthj normalize in ⊢ (%→?); * #H @False_ind @H %
    ]]
  | #Hci #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #rs0 #Hnthi >Hnthi in Hci;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #Hcj #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #rs0 #_ #Hnthj >Hnthj in Hcj;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #tc #td #te * #x * * * #Hendcx #Hci #Hcj #Hd #Hstar #IH #He lapply (IH He) -IH *
    #IH1 #IH2 %
    [ >Hci >Hcj * [* #x0 * #H destruct (H) >Hendcx #H destruct (H) 
    |* [* #H @False_ind [cases H -H #H @H % | destruct (H)] | #H destruct (H)]] 
    | #ls #c0 #xs #ci #rs #ls0 #rs0 cases xs
      [ #Hnthi #Hnthj #Hnotendc cases rs0 in Hnthj;
        [ #Hnthj % % // >IH1
          [ >Hd @eq_f3 //
            [ @eq_f3 // >(?:c0=x) [ >Hnthi % ]
              >Hnthi in Hci;normalize #H destruct (H) %
            | >(?:c0=x) [ >Hnthj % ]
              >Hnthi in Hci;normalize #H destruct (H) % ]
          | >Hd %2 %2 >nth_change_vec // >Hnthj % ]
        | #r1 #rs1 #Hnthj %2 %{r1} %{rs1} % // *
          [ #Hendci >IH1
            [ >Hd @eq_f3 // 
              [ @eq_f3 // >(?:c0=x) [ >Hnthi % ]
             >Hnthi in Hci;normalize #H destruct (H) %
            | >(?:c0=x) [ >Hnthj % ]
            >Hnthi in Hci;normalize #H destruct (H) % ]
        | >Hd >nth_change_vec // >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec // >Hnthi >Hnthj normalize % %{ci} % //
        ]
      |#Hcir1 >IH1
        [>Hd @eq_f3 // 
          [ @eq_f3 // >(?:c0=x) [ >Hnthi % ]
            >Hnthi in Hci;normalize #H destruct (H) %
          | >(?:c0=x) [ >Hnthj % ]
            >Hnthi in Hci;normalize #H destruct (H) % ]
        | >Hd %2 % % >nth_change_vec //
          >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec // >Hnthi >Hnthj normalize @(not_to_not … Hcir1)
          #H destruct (H) % ]
      ]
    ]
  |#x0 #xs0 #Hnthi #Hnthj #Hnotendc 
   cut (c0 = x) [ >Hnthi in Hci; normalize #H destruct (H) // ]
   #Hcut destruct (Hcut) cases rs0 in Hnthj;
    [ #Hnthj % % // 
      cases (IH2 (x::ls) x0 xs0 ci rs (x::ls0) [ ] ???) -IH2
      [ * #_ #IH2 >IH2 >Hd >change_vec_commute in ⊢ (??%?); //
        >change_vec_change_vec >change_vec_commute in ⊢ (??%?); //
        @sym_not_eq //
      | * #cj * #rs1 * #H destruct (H)
      | >Hd >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
        >Hnthi %
      | >Hd >nth_change_vec // >Hnthj %
      | #c0 #Hc0 @Hnotendc @memb_cons @Hc0 ]
    | #r1 #rs1 #Hnthj %2 %{r1} %{rs1} % // #Hcir1
      cases(IH2 (x::ls) x0 xs0 ci rs (x::ls0) (r1::rs1) ???)
      [ * #H destruct (H)
      | * #r1' * #rs1' * #H destruct (H) #Hc1r1 >Hc1r1 //
        >Hd >change_vec_commute in ⊢ (??%?); //
        >change_vec_change_vec >change_vec_commute in ⊢ (??%?); //
          @sym_not_eq //
      | >Hd >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
        >Hnthi //
      | >Hd >nth_change_vec // >Hnthi >Hnthj %
      | #c0 #Hc0 @Hnotendc @memb_cons @Hc0
]]]]]
qed.      
 
lemma terminate_compare :  ∀i,j,sig,n,is_endc,t.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n is_endc ↓ t.
#i #j #sig #n #is_endc #t #Hneq #Hi #Hj
@(terminate_while … (sem_comp_step …)) //
<(change_vec_same … t i (niltape ?))
cases (nth i (tape sig) t (niltape ?))
[ % #t1 * #x * * * #_ >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct 
|2,3: #a0 #al0 % #t1 * #x * * * #_ >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * * * #Hendcx >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #Hxsep >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * * * #Hendcx0 >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcur
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_compare : ∀i,j,sig,n,is_endc.
  i ≠ j → i < S n → j < S n → 
  compare i j sig n is_endc ⊨ R_compare i j sig n is_endc.
#i #j #sig #n #is_endc #Hneq #Hi #Hj @WRealize_to_Realize /2/
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
  compare src dst sig n is_endc ·
    (ifTM ?? (inject_TM ? (test_char ? (λa.is_endc a == false)) n src)
      (single_finalTM ??
        (parmove src dst sig n L is_startc · (inject_TM ? (move_r ?) n dst)))
      (nop …)
      tc_true).
      
definition Rtc_multi_true ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
   (∃c. current alpha (nth i ? t1 (niltape ?)) = Some ? c ∧ test c = true) ∧ t2 = t1.
   
definition Rtc_multi_false ≝ 
  λalpha,test,n,i.λt1,t2:Vector ? (S n).
    (∀c. current alpha (nth i ? t1 (niltape ?)) = Some ? c → test c = false) ∧ t2 = t1.

definition R_match_step_false ≝ 
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀ls,x,xs,end,rs.
  nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) →
  (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → is_endc end = true →
   ((current sig (nth dst (tape sig) int (niltape sig)) = None ?) ∧ outt = int) ∨
   (∃ls0,rs0. 
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) ∧
    ∀rsj,c. 
    rs0 = c::rsj →
    outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
           (midtape sig (reverse ? xs@x::ls0) c rsj) dst).
(*  
definition R_match_step_false ≝  
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
   (((∃x.current ? (nth src ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
     current sig (nth src (tape sig) int (niltape sig)) = None ? ∨
     current sig (nth dst (tape sig) int (niltape sig)) = None ? ) ∧ outt = int) ∨
   (∃ls,ls0,rs,rs0,x,xs. 
    nth src ? int (niltape ?) = midtape sig ls x (xs@rs) ∧ is_endc x = false ∧
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) ∧
    ∀rsi,rsj,end,c. 
    rs = end::rsi → rs0 = c::rsj →
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) ∧ is_endc end = true ∧
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@c::rsj) ∧
    outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rsi) src)
           (midtape sig (reverse ? xs@x::ls0) c rsj) dst).
*)

definition R_match_step_true ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀s.current sig (nth src (tape sig) int (niltape sig)) = Some ? s → 
  is_startc s = true → 
  (∀c.c ∈ right ? (nth src (tape sig) int (niltape sig)) = true → is_startc c = false) →
  (current sig (nth dst (tape sig) int (niltape sig)) = None ? → outt = int) ∧
  (∀s1.current sig (nth dst (tape sig) int (niltape sig)) = Some ? s1 → s ≠ s1 →  
   outt = change_vec ?? int 
          (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈s1,R〉)) dst ∧ is_endc s = false) ∧  
  (∀ls,x,xs,ci,rs,ls0,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) →
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → 
    (∃cj,rs1.rs0 = cj::rs1 → ci ≠ cj →
     (outt = change_vec ?? int 
           (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈x,R〉)) dst ∧ is_endc ci = false)) ∨
    (rs0 = [ ] →
     outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) src)
           (mk_tape sig (reverse ? xs@x::ls0) (None ?) [ ]) dst)).
           
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

axiom comp_list: ∀S:DeqSet. ∀l1,l2:list S.∀is_endc. ∃l,tl1,tl2. 
  l1 = l@tl1 ∧ l2 = l@tl2 ∧ (∀c.c ∈ l = true → is_endc c = false) ∧
  ∀a,tla. tl1 = a::tla → is_endc a = true ∨ (∀b,tlb.tl2 = b::tlb → a≠b).
  
axiom daemon : ∀X:Prop.X.

lemma sem_match_step :
  ∀src,dst,sig,n,is_startc,is_endc.src ≠ dst → src < S n → dst < S n → 
  match_step src dst sig n is_startc is_endc ⊨ 
    [ inr ?? (inr ?? (inl … (inr ?? start_nop))) : 
      R_match_step_true src dst sig n is_startc is_endc, 
      R_match_step_false src dst sig n is_endc ].
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst 
@(acc_sem_seq_app sig n … (sem_compare src dst sig n is_endc Hneq Hsrc Hdst)
    (acc_sem_if ? n … (sem_test_char_multi sig (λa.is_endc a == false) n src (le_S_S_to_le … Hsrc))
      (sem_seq … 
        (sem_parmoveL ???? is_startc Hneq Hsrc Hdst) 
        (sem_inject … dst (le_S_S_to_le … Hdst) (sem_move_r ? )))
      (sem_nop …)))
[#ta #tb #tc * #Hcomp1 #Hcomp2 * #td * * * #c * #Hcurtc #Hcend #Htd >Htd -Htd
 #Htb #s #Hcurta_src #Hstart #Hnotstart % [ %
 [#Hdst_none @daemon 
 | #s1 #Hcurta_dst #Hneqss1
   lapply Htb lapply Hcurtc -Htb -Hcurtc >(?:tc=ta) 
   [|@Hcomp1 %2 % % >Hcurta_src >Hcurta_dst @(not_to_not … Hneqss1) #H destruct (H) % ]
   #Hcurtc * #te * * #_ #Hte >Hte [2: %1 %1 %{s} % //] 
   whd in ⊢ (%→?); * * #_ #Htbdst #Htbelse %
   [ @(eq_vec … (niltape ?)) #i #Hi cases (decidable_eq_nat i dst) #Hidst
     [ >Hidst >nth_change_vec // cases (current_to_midtape … Hcurta_dst)
       #ls * #rs #Hta_mid >(Htbdst … Hta_mid) >Hta_mid cases rs //
     | >nth_change_vec_neq [|@sym_not_eq //] @sym_eq @Htbelse @sym_not_eq // ]
   | >Hcurtc in Hcurta_src; #H destruct (H) cases (is_endc s) in Hcend;
     normalize #H destruct (H) // ]
   ]
 |#ls #x #xs #ci #rs #ls0 #rs00 #Htasrc_mid #Htadst_mid #Hnotendc 
  cases rs00 in Htadst_mid;
   [(* case rs empty *) #Htadst_mid %2 #_
    cases (Hcomp2 … Htasrc_mid Htadst_mid Hnotendc) -Hcomp2 
     [2: * #x0 * #rs1 * #H destruct (H) ]
    * #_ #Htc cases Htb #td * * #_ #Htd >Htasrc_mid in Hcurta_src; 
    normalize in ⊢ (%→?); #H destruct (H)  
    >Htd [2: %2 >Htc >nth_change_vec // cases (reverse sig ?) //]
    >Htc * * >nth_change_vec // #Htbdst #_ #Htbelse
     @(eq_vec … (niltape ?)) #i #Hi cases (decidable_eq_nat i dst) #Hidst
      [ >Hidst >nth_change_vec // <Htbdst // cases (reverse sig ?) //
      |@sym_eq @Htbelse @sym_not_eq //
      ] 
    |#cj #rs0 #Htadst_mid % %{cj} %{rs0} #_ #Hcicj
    cases (Hcomp2 … Htasrc_mid Htadst_mid Hnotendc) [ * #H destruct (H) ]
    * #cj' * #rs0' * #Hcjrs0 destruct (Hcjrs0) -Hcomp2 #Hcomp2
    lapply (Hcomp2 (or_intror ?? Hcicj)) -Hcomp2 #Htc
    cases Htb #td * * #Htd #_ >Htasrc_mid in Hcurta_src; normalize in ⊢ (%→?);
    #H destruct (H)
    >(Htd ls ci (reverse ? xs) rs s ??? ls0 cj' (reverse ? xs) s rs0' (refl ??)) //
    [| >Htc >nth_change_vec //
    | #c0 #Hc0 @(Hnotstart c0) >Htasrc_mid 
      cases (orb_true_l … Hc0) -Hc0 #Hc0
      [@memb_append_l2 >(\P Hc0) @memb_hd
      |@memb_append_l1 <(reverse_reverse …xs) @memb_reverse //
      ]
    | >Htc >nth_change_vec_neq [|@sym_not_eq // ] @nth_change_vec // ]
    * * #_ #Htbdst #Htbelse %
    [ @(eq_vec … (niltape ?)) #i #Hi cases (decidable_eq_nat i dst) #Hidst
       [ >Hidst >nth_change_vec // >Htadst_mid >(Htbdst ls0 s (xs@cj'::rs0'))
         [ cases xs //
         | >nth_change_vec // ]
       | >nth_change_vec_neq [|@sym_not_eq //]
         <Htbelse [|@sym_not_eq // ]
         >nth_change_vec_neq [|@sym_not_eq //]
         cases (decidable_eq_nat i src) #Hisrc
         [ >Hisrc >nth_change_vec // >Htasrc_mid //
         | >nth_change_vec_neq [|@sym_not_eq //]
           <(Htbelse i) [|@sym_not_eq // ]
           >Htc >nth_change_vec_neq [|@sym_not_eq // ]
           >nth_change_vec_neq [|@sym_not_eq // ] //
         ]
       ]
    | >Htc in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //] 
       >nth_change_vec // whd in ⊢ (??%?→?); 
       #H destruct (H) cases (is_endc c) in Hcend;
       normalize #H destruct (H) // ]
    ]
  ]
|#intape #outtape #ta * #Hcomp1 #Hcomp2 * #tb * * #Hc #Htb 
 whd in ⊢ (%→?); #Hout >Hout >Htb whd
 #ls #c_src #xs #end #rs #Hmid_src #Hnotend #Hend
 lapply (current_to_midtape sig (nth dst ? intape (niltape ?)))
 cases (current … (nth dst ? intape (niltape ?))) in Hcomp1;
  [#Hcomp1 #_ %1 % [% | @Hcomp1 %2 %2 % ]
  |#c_dst cases (true_or_false (c_src == c_dst)) #Hceq
    [#_ #Hmid_dst cases (Hmid_dst c_dst (refl …)) -Hmid_dst
     #ls_dst * #rs_dst #Hmid_dst %2
     cases (comp_list … (xs@end::rs) rs_dst is_endc) #xs1 * #rsi * #rsj * * * 
     #Hrs_src #Hrs_dst #Hnotendxs1 #Hneq %{ls_dst} %{rsj} >Hrs_dst in Hmid_dst; #Hmid_dst
     cut (∃r1,rs1.rsi = r1::rs1) [@daemon] * #r1 * #rs1 #Hrs1 >Hrs1 in Hrs_src;
     #Hrs_src >Hrs_src in Hmid_src; #Hmid_src <(\P Hceq) in Hmid_dst; #Hmid_dst
     lapply (Hcomp2 ??????? Hmid_src Hmid_dst ?) 
     [ #c0 #Hc0 cases (orb_true_l … Hc0) -Hc0 #Hc0
       [ >(\P Hc0) @Hnotend @memb_hd | @Hnotendxs1 //]
     | *
       [ * #Hrsj #Hta %
         [ >Hta in Hc; >nth_change_vec_neq [|@sym_not_eq //] >nth_change_vec //
           #Hc lapply (Hc ? (refl ??)) #Hendr1
           cut (xs = xs1)
           [ lapply Hnotendxs1 lapply Hnotend lapply Hrs_src lapply xs1
             -Hnotendxs1 -Hnotend -Hrs_src -xs1 elim xs
             [ * normalize in ⊢ (%→?); //
               #x2 #xs2 normalize in ⊢ (%→?); #Heq destruct (Heq) #_ #Hnotendxs1
               lapply (Hnotendxs1 ? (memb_hd …)) >Hend #H destruct (H)
             | #x2 #xs2 #IH *
               [ normalize in ⊢ (%→?); #Heq destruct (Heq) #Hnotendc
                 >Hnotendc in Hendr1; [| @memb_cons @memb_hd ]
                 normalize in ⊢ (%→?); #H destruct (H)
               | #x3 #xs3 normalize in ⊢ (%→?); #Heq destruct (Heq)
                 #Hnotendc #Hnotendcxs1 @eq_f @IH
                 [ @(cons_injective_r … Heq)
                 | #c0 #Hc0 @Hnotendc cases (orb_true_l … Hc0) -Hc0 #Hc0
                   [ >(\P Hc0) @memb_hd
                   | @memb_cons @memb_cons // ]
                 | #c #Hc @Hnotendcxs1 @memb_cons // ]
               ]
             ]
           | #Hxsxs1 >Hmid_dst >Hxsxs1 % ]
         | #rsj0 #c >Hrsj #Hrsj0 destruct (Hrsj0) ]
       | * #cj * #rs2 * #Hrs2 #Hta lapply (Hta ?) 
         [ cases (Hneq … Hrs1) /2/ #H %2 @(H ?? Hrs2) ]
         -Hta #Hta >Hta in Hc; >nth_change_vec_neq [|@sym_not_eq //] 
         >nth_change_vec // #Hc lapply (Hc ? (refl ??)) #Hendr1
         (* lemmatize this proof *) cut (xs = xs1)
         [ lapply Hnotendxs1 lapply Hnotend lapply Hrs_src lapply xs1
           -Hnotendxs1 -Hnotend -Hrs_src -xs1 elim xs
           [ * normalize in ⊢ (%→?); //
             #x2 #xs2 normalize in ⊢ (%→?); #Heq destruct (Heq) #_ #Hnotendxs1
             lapply (Hnotendxs1 ? (memb_hd …)) >Hend #H destruct (H)
           | #x2 #xs2 #IH *
             [ normalize in ⊢ (%→?); #Heq destruct (Heq) #Hnotendc
               >Hnotendc in Hendr1; [| @memb_cons @memb_hd ]
               normalize in ⊢ (%→?); #H destruct (H)
             | #x3 #xs3 normalize in ⊢ (%→?); #Heq destruct (Heq)
               #Hnotendc #Hnotendcxs1 @eq_f @IH
               [ @(cons_injective_r … Heq)
               | #c0 #Hc0 @Hnotendc cases (orb_true_l … Hc0) -Hc0 #Hc0
                 [ >(\P Hc0) @memb_hd
                 | @memb_cons @memb_cons // ]
               | #c #Hc @Hnotendcxs1 @memb_cons // ]
             ]
           ]
         | #Hxsxs1 >Hmid_dst >Hxsxs1 % //
           #rsj0 #c #Hcrsj destruct (Hxsxs1 Hrs2 Hcrsj) @eq_f3 //
           @eq_f3 // lapply (append_l2_injective ?????? Hrs_src) //
           #Hendr1 destruct (Hendr1) % ]
       ]
     ]
   (* STOP *)
   |#Hcomp1 #Hsrc cases (Hsrc ? (refl ??)) -Hsrc #ls0 * #rs0 #Hdst 
    @False_ind lapply (Hcomp1 ?) [%2 %1 %1 >Hmid_src normalize
    @(not_to_not ??? (\Pf Hceq)) #H destruct //] #Hintape 
    >Hintape in Hc; >Hmid_src #Hc lapply (Hc ? (refl …)) -Hc 
    >(Hnotend c_src) // normalize #H destruct (H)   
   ]
  ]
]
qed. 

definition match_m ≝ λsrc,dst,sig,n,is_startc,is_endc.
  whileTM … (match_step src dst sig n is_startc is_endc) 
    (inr ?? (inr ?? (inl … (inr ?? start_nop)))).

definition R_match_m ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀ls,x,xs,end,rs.
  nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) →
  is_startc x = true →
  (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → is_endc end = true →
   ((current sig (nth dst (tape sig) int (niltape sig)) = None ?) →
     current sig (nth dst (tape sig) outt (niltape sig)) = None ?)
     (* outt = int) *) ∧
   (∀ls0,x0,rs0.
    nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃l,l1.x0::rs0 = l@x::xs@l1 ∧
     ∀cj,l2.l1=cj::l2 →
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
            (midtape sig ((reverse ? (l@x::xs))@ls0) cj l2) dst) ∨
    ∀l,l1.x0::rs0 ≠ l@x::xs@l1).

(*
definition R_match_m ≝ 
  λi,j,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  (((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,xs,ci,rs,ls0,x0,rs0.
    (∀x. is_startc x ≠ is_endc x) → 
    is_startc x = true → is_endc ci = true → 
    (∀z. memb ? z (x::xs) = true → is_endc x = false) →
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃l,l1.x0::rs0 = l@x::xs@l1 ∧
     ∀cj,l2.l1=cj::l2 →
     outt = change_vec ?? 
            (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
            (midtape sig ((reverse ? (l@x::xs))@ls0) cj l2) j) ∨
    ∀l,l1.x0::rs0 ≠ l@x::xs@l1).
*)

(*
axiom sub_list_dec: ∀A.∀l,ls:list A. 
  ∃l1,l2. l = l1@ls@l2 ∨ ∀l1,l2. l ≠ l1@ls@l2.
*)

lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc #Hfalse #ls #x #xs #end #rs #Hmid_src #Hstart #Hnotend #Hend
  cases (Hfalse … Hmid_src Hnotend Hend) -Hfalse 
  [(* current dest = None *) * #Hcur_dst #Houtc %
    [#_ >Houtc //
    |#ls0 #x0 #rs0 #Hmid_dst >Hmid_dst in Hcur_dst; 
     normalize in ⊢ (%→?); #H destruct (H)
    ]
  |* #ls0 * #rs0 * #Hmid_dst #HFalse %
    [ >Hmid_dst normalize in ⊢ (%→?); #H destruct (H)
    |#ls1 #x1 #rs1 >Hmid_dst #H destruct (H)
     %1 %{[ ]} %{rs0} % [%] #cj #l2 #Hnotnil 
     >reverse_cons >associative_append @(HFalse ?? Hnotnil)
    ]
  ]
|#ta #tb #tc #Htrue #Hstar #IH #Hout lapply (IH Hout) -IH -Hout #IH whd
 #ls #x #xs #end #rs #Hmid_src #Hstart #Hnotend #Hend 
 lapply (refl ? (current ? (nth dst ? ta (niltape ?))))
 cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→?); 
  [#Hmid_dst % [#_ whd in Htrue; >Hmid_src in Htrue; #Htrue
   cases (Htrue x (refl … ) Hstart ?) -Htrue [2: @daemon]
   * #Htb #_ #_ >Htb in IH; // #IH  
   cases (IH ls x xs end rs Hmid_src Hstart Hnotend Hend)
    [#H @H //
    |
   
  |#cur_dst #Hcur_dst %2 #ls0 #x0 #rs0 #Hmid_dst 
   whd in Htrue; >Hmid_src in Htrue; #Htrue
   cases (Htrue x (refl …) Hstart ?) -Htrue
    [2: #z #membz @daemon (*aggiungere l'ipotesi*)]
   cases (true_or_false (x==cur_dst)) #eqx
    [#_ #Htrue cases (comp_list ? (xs@end::rs) rs0 is_endc)
     #x1 * #tl1 * #tl2 * * * #Hxs #Hrs0 #Hnotendx1
     cases tl1 in Hxs; 
      [>append_nil #Hx1 @daemon (* absurd by Hxs e notendx1 *)]
     #ci -tl1 #tl1 #Hxs #H cases (H … (refl … ))
      [(* this is absurd, since Htrue conlcudes is_endc ci =false *)
       #Hend_ci 
      
    @daemon (* lapply(Htrue … (refl …)) -Htrue *)
    |#Htrue #_ cases(Htrue cur_dst Hcur_dst (\Pf eqx)) -Htrue #Htb #Hendx
     whd in IH;
     cases(IH ls x xs end rs ? Hstart Hnotend Hend)
      [* #H1 #H2 >Htb in H1; >nth_change_vec // 
       >Hmid_dst cases rs0 [2: #a #tl normalize in ⊢ (%→?); #H destruct (H)] 
       #_ %2 @daemon (* si dimostra *)
      |@daemon
      |>Htb >nth_change_vec_neq [|@sym_not_eq //] @Hmid_src
      ] 
    ]
  ]
]
qed.

