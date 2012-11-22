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
  (∀ls,x,xs,ci,rs,ls0,cj,rs0. 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x (xs@cj::rs0) →
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → 
    (is_endc ci = true ∨ ci ≠ cj) → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (midtape sig (reverse ? xs@x::ls0) cj rs0) j).
          
lemma wsem_compare : ∀i,j,sig,n,is_endc.i ≠ j → i < S n → j < S n → 
  compare i j sig n is_endc ⊫ R_compare i j sig n is_endc.
#i #j #sig #n #is_endc #Hneq #Hi #Hj #ta #k #outc #Hloop
lapply (sem_while … (sem_comp_step i j sig n is_endc Hneq Hi Hj) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * * [ * [ *
  [* #curi * #Hcuri #Hendi #Houtc %
    [ #_ @Houtc  
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hnthi #Hnthj #Hnotendc 
      @False_ind
      >Hnthi in Hcuri; normalize in ⊢ (%→?); #H destruct (H)
      >(Hnotendc ? (memb_hd … )) in Hendi; #H destruct (H)
    ]
  |#Hcicj #Houtc % 
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hnthi #Hnthj
      >Hnthi in Hcicj; >Hnthj normalize in ⊢ (%→?); * #H @False_ind @H %
    ]]
  | #Hci #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hnthi >Hnthi in Hci;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #Hcj #Houtc %
    [ #_ @Houtc
    | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #Hnthj >Hnthj in Hcj;
      normalize in ⊢ (%→?); #H destruct (H) ] ]
  | #tc #td #te * #x * * * #Hendcx #Hci #Hcj #Hd #Hstar #IH #He lapply (IH He) -IH *
    #IH1 #IH2 %
    [ >Hci >Hcj * [* #x0 * #H destruct (H) >Hendcx #H destruct (H) 
    |* [* #H @False_ind [cases H -H #H @H % | destruct (H)] | #H destruct (H)]] 
    | #ls #c0 #xs #ci #rs #ls0 #cj #rs0 cases xs
      [ #Hnthi #Hnthj #Hnotendc #Hcicj >IH1 
        [ >Hd @eq_f3 // 
          [ @eq_f3 // >(?:c0=x) [ >Hnthi % ]
            >Hnthi in Hci;normalize #H destruct (H) %
          | >(?:c0=x) [ >Hnthj % ]
            >Hnthi in Hci;normalize #H destruct (H) % ]
        | >Hd >nth_change_vec // >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec // >Hnthi >Hnthj normalize 
          cases Hcicj #Hcase 
          [%1 %{ci} % // | %2 %1 %1 @(not_to_not ??? Hcase) #H destruct (H) % ]
        ]
      | #x0 #xs0 #Hnthi #Hnthj #Hnotendc #Hcicj
        >(IH2 (c0::ls) x0 xs0 ci rs (c0::ls0) cj rs0 … Hcicj)
        [ >Hd >change_vec_commute in ⊢ (??%?); //
          >change_vec_change_vec >change_vec_commute in ⊢ (??%?); //
          @sym_not_eq //
        | #c1 #Hc1 @Hnotendc @memb_cons @Hc1
        | >Hd >nth_change_vec // >Hnthj normalize
          >Hnthi in Hci;normalize #H destruct (H) %
        | >Hd >nth_change_vec_neq [|@sym_not_eq //] >Hnthi
          >nth_change_vec // normalize
          >Hnthi in Hci;normalize #H destruct (H) %
        ]
]]]
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

axiom comp_list: ∀S:DeqSet. ∀l1,l2:list S.∀is_endc. ∃l,tl1,tl2. 
  l1 = l@tl1 ∧ l2 = l@tl2 ∧ (∀c.c ∈ l = true → is_endc c = false) ∧
  ∀a,tla. tl1 = a::tla → is_endc a = true ∨ (∀b,tlb.tl2 = b::tlb → a≠b).

   
definition R_match_step_false ≝  
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
   (((∃x.current ? (nth src ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
     (* current ? (nth src ? int (niltape ?)) ≠ current ? (nth dst ? int (niltape ?)) ∨ *)   
     current sig (nth src (tape sig) int (niltape sig)) = None ? ∨
     current sig (nth dst (tape sig) int (niltape sig)) = None ? ) → outt = int) ∧
   (∀ls,ls0,x,x0,rs,rs0.
     nth src ? int (niltape ?) = midtape sig ls x rs → 
     nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 → 
     x ≠ x0 ∨
     (x = x0 ∧
      ∀xs,end,rs',rs0'.rs = xs@end::rs' → rs0 = xs@rs0' → 
      (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) →
      is_endc end = false ∨
      (is_endc end = true ∧
      outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
           (mk_tape sig (reverse ? xs@x::ls0) (option_hd ? rs0) (tail ? rs0)) dst))).
   
     ∀ls,ls0,rs,rs0,x,xs,end. 
     (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) →
     nth src ? int (niltape ?) = midtape sig ls x (xs@end::rs) → 
     nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) → 
     is_endc end = false ∨
     (is_endc end = true ∧
      outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rs) src)
           (mk_tape sig (reverse ? xs@x::ls0) (option_hd ? rs0) (tail ? rs0)) dst)).

(*
definition R_match_step_false ≝  
  λsrc,dst,sig,n,is_endc.λint,outt: Vector (tape sig) (S n).
   (((∃x.current ? (nth src ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
     (* current ? (nth src ? int (niltape ?)) ≠ current ? (nth dst ? int (niltape ?)) ∨ *)   
     current sig (nth src (tape sig) int (niltape sig)) = None ? ∨
     current sig (nth dst (tape sig) int (niltape sig)) = None ? ) ∧ outt = int) ∨
   ∃ls,ls0,rs,rs0,x,xs. ∀rsi,rsj,end,c. 
    rs = end::rsi → rs0 = c::rsj →
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) ∧ is_endc end = true ∧
    nth src ? int (niltape ?) = midtape sig ls x (xs@rs) ∧
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) ∧
    outt = change_vec ??
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) end rsi) src)
           (midtape sig (reverse ? xs@x::ls0) c rsj) dst.

*)

definition R_match_step_true ≝ 
  λsrc,dst,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀s.current sig (nth src (tape sig) int (niltape sig)) = Some ? s → 
  is_startc s = true → 
  (∀c.c ∈ right ? (nth src (tape sig) int (niltape sig)) = true → is_startc c = false) →
  (∀s1.current sig (nth dst (tape sig) int (niltape sig)) = Some ? s1 → s ≠ s1 →  
   outt = change_vec ?? int 
          (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈s1,R〉)) dst ∧ is_endc s = false) ∧  
  (∀ls,x,xs,ci,rs,ls0,cj,rs0. 
    nth src ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth dst ? int (niltape ?) = midtape sig ls0 x (xs@cj::rs0) → ci ≠ cj → 
    (∀c0. memb ? c0 (x::xs) = true → is_endc c0 = false) → 
    outt = change_vec ?? int 
           (tape_move … (nth dst ? int (niltape ?)) (Some ? 〈x,R〉)) dst ∧ is_endc ci = false).
    
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
@daemon
(*
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst 
@(acc_sem_seq_app sig n … (sem_compare src dst sig n is_endc Hneq Hsrc Hdst)
    (acc_sem_if ? n … (sem_test_char_multi sig (λa.is_endc a == false) n src (le_S_S_to_le … Hsrc))
      (sem_seq … 
        (sem_parmoveL ???? is_startc Hneq Hsrc Hdst) 
        (sem_inject … dst (le_S_S_to_le … Hdst) (sem_move_r ? )))
      (sem_nop …)))
[#ta #tb #tc * #Hcomp1 #Hcomp2 * #td * * * #c * #Hcurtc #Hcend #Htd >Htd -Htd
 #Htb #s #Hcurta_src #Hstart #Hnotstart %
 [ #s1 #Hcurta_dst #Hneqss1
   lapply Htb lapply Hcurtc -Htb -Hcurtc >(?:tc=ta) 
   [|@Hcomp1 %2 % % >Hcurta_src >Hcurta_dst @(not_to_not … Hneqss1) #H destruct (H) % ]
   #Hcurtc * #te * * #_ #Hte >Hte // whd in ⊢ (%→?); * * #_ #Htbdst #Htbelse %
   [ @(eq_vec … (niltape ?)) #i #Hi cases (decidable_eq_nat i dst) #Hidst
     [ >Hidst >nth_change_vec // cases (current_to_midtape … Hcurta_dst)
       #ls * #rs #Hta_mid >(Htbdst … Hta_mid) >Hta_mid cases rs //
     | >nth_change_vec_neq [|@sym_not_eq //] @sym_eq @Htbelse @sym_not_eq // ]
   | >Hcurtc in Hcurta_src; #H destruct (H) cases (is_endc s) in Hcend;
     normalize #H destruct (H) // ]
 |#ls #x #xs #ci #rs #ls0 #cj #rs0 #Htasrc_mid #Htadst_mid #Hcicj #Hnotendc
  lapply (Hcomp2 … Htasrc_mid Htadst_mid Hnotendc (or_intror ?? Hcicj))
  -Hcomp2 #Hcomp2
  cases Htb #td * * #Htd #_ >Htasrc_mid in Hcurta_src; normalize in ⊢ (%→?);
  #H destruct (H)
  >(Htd ls ci (reverse ? xs) rs s ??? ls0 cj (reverse ? xs) s rs0 (refl ??)) //
  [| >Hcomp2 >nth_change_vec //
   | #c0 #Hc0 @(Hnotstart c0) >Htasrc_mid 
     cases (orb_true_l … Hc0) -Hc0 #Hc0
    [@memb_append_l2 >(\P Hc0) @memb_hd
    |@memb_append_l1 <(reverse_reverse …xs) @memb_reverse //
    ]
   | >Hcomp2 >nth_change_vec_neq [|@sym_not_eq // ] @nth_change_vec // ]
  * * #_ #Htbdst #Htbelse %
  [ @(eq_vec … (niltape ?)) #i #Hi cases (decidable_eq_nat i dst) #Hidst
     [ >Hidst >nth_change_vec // >Htadst_mid >(Htbdst ls0 s (xs@cj::rs0))
       [ cases xs //
       | >nth_change_vec // ]
     | >nth_change_vec_neq [|@sym_not_eq //]
       <Htbelse [|@sym_not_eq // ]
       >nth_change_vec_neq [|@sym_not_eq //]
        (* STOP. *)
       cases (decidable_eq_nat i src) #Hisrc
       [ >Hisrc >nth_change_vec // >Htasrc_mid //
       | >nth_change_vec_neq [|@sym_not_eq //]
         <(Htbelse i) [|@sym_not_eq // ]
         >Hcomp2 >nth_change_vec_neq [|@sym_not_eq // ]
         >nth_change_vec_neq [|@sym_not_eq // ] //
       ]
     ]
  | >Hcomp2 in Hcurtc; >nth_change_vec_neq [|@sym_not_eq //] 
     >nth_change_vec // whd in ⊢ (??%?→?); 
     #H destruct (H) cases (is_endc c) in Hcend;
     normalize #H destruct (H) // ]
  ]
|#intape #outtape #ta * #Hcomp1 #Hcomp2 * #tb * * #Hc #Htb 
 whd in ⊢ (%→?); #Hout >Hout >Htb whd
 lapply (current_to_midtape sig (nth src ? intape (niltape ?)))
 cases (current … (nth src ? intape (niltape ?))) in Hcomp1; 
  [#Hcomp1 #_ %1 % [%1 %2 // | @Hcomp1 %2 %1 %2 %]
  |#c_src lapply (current_to_midtape sig (nth dst ? intape (niltape ?)))
   cases (current … (nth dst ? intape (niltape ?))) 
    [#_ #Hcomp1 #_ %1 % [%2 % | @Hcomp1 %2 % % % #H destruct (H)]
    |#c_dst cases (true_or_false (c_src == c_dst)) #Hceq
      [#Hmid_dst cases (Hmid_dst c_dst (refl …)) -Hmid_dst
       #ls_dst * #rs_dst #Hmid_dst #Hcomp1
       #Hmid_src cases (Hmid_src c_src (refl …)) -Hmid_src
       #ls_src * #rs_src #Hmid_src
       cases (true_or_false (is_endc c_src)) #Hc_src
       [ % % [ % % %{c_src} % // | @Hcomp1 % %{c_src} % // ]
       | %2 cases (comp_list … rs_src rs_dst is_endc) #xs * #rsi * #rsj * * * 
         #Hrs_src #Hrs_dst #Hnotendc #Hneq    
         %{ls_src} %{ls_dst} %{rsi} %{rsj} %{c_src} %{xs} 
         #rsi0 #rsj0 #end #c #Hend #Hc_dst
         >Hrs_src in Hmid_src; >Hend #Hmid_src
         >Hrs_dst in Hmid_dst; >Hc_dst <(\P Hceq) #Hmid_dst
         cut (is_endc end = true ∨ end ≠ c)
         [cases (Hneq … Hend) /2/ -Hneq #Hneq %2 @(Hneq … Hc_dst) ] #Hneq
         lapply (Hcomp2 … Hmid_src Hmid_dst ? Hneq)
          [#c0 #Hc0 cases (orb_true_l … Hc0) -Hc0 #Hc0
            [ >(\P Hc0) //
            | @Hnotendc // ] 
          ]
         -Hcomp2 #Hcomp2 <Hcomp2
         % // % [ % 
         [>Hcomp2 in Hc; >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec // #H lapply (H ? (refl …)) 
          cases (is_endc end) [|normalize #H destruct (H) ]
          #_ % // #c0 #Hc0 cases (orb_true_l … Hc0) -Hc0 #Hc0
          [ >(\P Hc0) // | @Hnotendc // ]
         |@Hmid_src]
         |@Hmid_dst] ]
      |#_ #Hcomp1 #Hsrc cases (Hsrc ? (refl ??)) -Hsrc #ls * #rs #Hsrc
       %1 % 
        [% % %{c_src} % // lapply (Hc c_src) -Hc >Hcomp1
         [| %2 % % @(not_to_not ??? (\Pf Hceq)) #H destruct (H) // ]
         cases (is_endc c_src) //
         >Hsrc #Hc lapply (Hc (refl ??)) normalize #H destruct (H)
        |@Hcomp1 %2 %1 %1 @(not_to_not ??? (\Pf Hceq)) #H destruct (H) //
        ]
      ]
    ]
  ] 
*)
qed.

definition match_m ≝ λsrc,dst,sig,n,is_startc,is_endc.
  whileTM … (match_step src dst sig n is_startc is_endc) 
    (inr ?? (inr ?? (inl … (inr ?? start_nop)))).

(*
definition R_match_m ≝ 
  λi,j,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  ∀ls,x,rs,ls0,x0,rs0.
    nth i ? int (niltape ?) = midtape sig ls x rs →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    
  ,xs,ci,rs,ls0,x0,rs0. 
    is_startc x = true → is_endc ci = true → 
    (∀c0.c0 ∈ (x::xs) = true → is_endc c0 = false) → 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
   
  (((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,xs,ci,rs,ls0,x0,rs0. 
    is_startc x = true → is_endc ci = true → 
    (∀c0.c0 ∈ (x::xs) = true → is_endc c0 = false) → 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    ∃l,cj,l1.x0::rs0 = l@x::xs@cj::l1 ∧
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (midtape sig ((reverse ? (l@x::xs))@ls0) cj l1) j).
           
lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * 
  [ * * [ *
    [ * #cur_src * #H1 #H2 #Houtc %   
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #Hnotendc #Hnthsrc
        @False_ind >Hnthsrc in H1;normalize
        #H1 destruct (H1) >(Hnotendc ? (memb_hd …)) in H2; #H2 destruct (H2)
      ]
    | #Hci #Houtc %
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hstart #Hend_ci #Hnotend 
        #Hnthi >Hnthi in Hci; normalize in ⊢ (%→?); #H destruct (H) ] ]
    | #Hcj #Houtc %
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #_ #_ #Hnthj >Hnthj in Hcj;
        normalize in ⊢ (%→?); #H destruct (H) ] ]
  | * #ls * #ls0 * #rs * #rs0 * #x * #xs #Houtc %
    [ Houtc ?? x x (refl ??) (refl ??))
     #Hcases 
      cut (∃end,rsi.rs = end::rsi ∧ nth src ? tc (niltape ?) = midtape ? ls x (xs@rs))
      [ cases (nth src ? tc (niltape ?)) in


lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * 
  [ * * [ *
    [ * #cur_src * #H1 #H2 #Houtc %   
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #Hnthi #Hnthj
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



[ #tc whd in ⊢ (%→?); * * [ *

*)

definition R_match_m ≝ 
  λi,j,sig,n,is_startc,is_endc.λint,outt: Vector (tape sig) (S n).
  (((∃x.current ? (nth i ? int (niltape ?)) = Some ? x ∧ is_endc x = true) ∨
    current ? (nth i ? int (niltape ?)) = None ? ∨
    current ? (nth j ? int (niltape ?)) = None ?) → outt = int) ∧
  (∀ls,x,xs,ci,rs,ls0,x0,rs0. 
    is_startc x = true → is_endc ci = true → 
    (∀c0.c0 ∈ (x::xs) = true → is_endc c0 = false) → 
    nth i ? int (niltape ?) = midtape sig ls x (xs@ci::rs) →
    nth j ? int (niltape ?) = midtape sig ls0 x0 rs0 →
    (∃x1. is_endc x1 = false ∧ current ? (nth i ? outt (niltape ?)) = Some ? x1) ∨
     (∃l,cj,l1.x0::rs0 = l@x::xs@cj::l1 ∧
      outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) ci rs) i)
           (midtape sig ((reverse ? (l@x::xs))@ls0) cj l1) j)).
           
lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * #HR1 #HR2 % [ @HR1 ]
  #ls #x #xs #ci #rs #ls0 #x0 #rs0 #Hstartc #Hendc #Hnotendc #Hsrctc #Hdsttc
  cases (comp_list ? (x::xs@ci::rs) (x0::rs0) is_endc)
  #l0 * #l1 * #l2 * * * #Heqsrc #Heqdst #Hnotendsrc #Hor
  cut (∃x1,l1'.l1 = x1::l1') [@daemon] * #x1 * #l1' #Hl1
  cases (Hor ?? Hl1) -Hor
  [
  cases HR2 -HR2 #HR2 [% @HR2]
  |cut (is_endc x1 = false) [@daemon] #Hx1
  
  
  [ * * [ *
    [ * #cur_src * #H1 #H2 #Houtc %   
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #Hnotendc #Hnthsrc
        @False_ind >Hnthsrc in H1;normalize
        #H1 destruct (H1) >(Hnotendc ? (memb_hd …)) in H2; #H2 destruct (H2)
      ]
    | #Hci #Houtc %
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #Hstart #Hend_ci #Hnotend 
        #Hnthi >Hnthi in Hci; normalize in ⊢ (%→?); #H destruct (H) ] ]
    | #Hcj #Houtc %
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #_ #_ #Hnthj >Hnthj in Hcj;
        normalize in ⊢ (%→?); #H destruct (H) ] ]
  | * #ls * #ls0 * #rs * #rs0 * #x * #xs #Houtc %
    [ Houtc ?? x x (refl ??) (refl ??))
     #Hcases 
      cut (∃end,rsi.rs = end::rsi ∧ nth src ? tc (niltape ?) = midtape ? ls x (xs@rs))
      [ cases (nth src ? tc (niltape ?)) in Hcases;
        [


lemma wsem_match_m : ∀src,dst,sig,n,is_startc,is_endc.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n is_startc is_endc ⊫ R_match_m src dst sig n is_startc is_endc.
#src #dst #sig #n #is_startc #is_endc #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n is_startc is_endc Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #tc whd in ⊢ (%→?); * 
  [ * * [ *
    [ * #cur_src * #H1 #H2 #Houtc %   
      [ #_ @Houtc
      | #ls #x #xs #ci #rs #ls0 #cj #rs0 #_ #_ #Hnthi #Hnthj
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



[ #tc whd in ⊢ (%→?); * * [ *

