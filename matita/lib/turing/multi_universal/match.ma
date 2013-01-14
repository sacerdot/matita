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

include "turing/multi_universal/compare.ma".
include "turing/multi_universal/par_test.ma".
include "turing/multi_universal/moves_2.ma".

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

definition Rm_test_null_true ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
   current alpha (nth i ? t1 (niltape ?)) ≠ None ? ∧ t2 = t1.
   
definition Rm_test_null_false ≝ 
  λalpha,n,i.λt1,t2:Vector ? (S n).
    current alpha (nth i ? t1 (niltape ?)) = None ? ∧ t2 = t1.

lemma sem_test_null_multi : ∀alpha,n,i.i ≤ n → 
  inject_TM ? (test_null ?) n i ⊨ 
    [ tc_true : Rm_test_null_true alpha n i, Rm_test_null_false alpha n i ].
#alpha #n #i #Hin #int
cases (acc_sem_inject … Hin (sem_test_null alpha) int)
#k * #outc * * #Hloop #Htrue #Hfalse %{k} %{outc} % [ %
[ @Hloop
| #Hqtrue lapply (Htrue Hqtrue) * * #Hcur #Hnth_i #Hnth_j % //
  @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) #Hi0i
  [ >Hi0i @sym_eq @Hnth_i | @sym_eq @Hnth_j @sym_not_eq // ] ] 
| #Hqfalse lapply (Hfalse Hqfalse) * * #Hcur #Hnth_i #Hnth_j %
  [ @Hcur
  | @(eq_vec … (niltape ?)) #i0 #Hi0 cases (decidable_eq_nat i0 i) // 
    #Hi0i @sym_eq @Hnth_j @sym_not_eq // ] ] 
qed.

definition match_test ≝ λsrc,dst.λsig:DeqSet.λn.λv:Vector ? n.
  match (nth src (option sig) v (None ?)) with 
  [ None ⇒  false 
  | Some x ⇒  notb (nth dst (DeqOption sig) v (None ?) == None ?) ].

definition mmove_states ≝ initN 2.

definition mmove0 : mmove_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition mmove1 : mmove_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition trans_mmove ≝ 
 λi,sig,n,D.
 λp:mmove_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in match (pi1 … q) with
 [ O ⇒ 〈mmove1,change_vec ? (S n) (null_action ? n) (〈None ?,D〉) i〉
 | S _ ⇒ 〈mmove1,null_action sig n〉 ].

definition mmove ≝ 
  λi,sig,n,D.
  mk_mTM sig n mmove_states (trans_mmove i sig n D) 
    mmove0 (λq.q == mmove1).
    
definition Rm_multi ≝ 
  λalpha,n,i,D.λt1,t2:Vector ? (S n).
  t2 = change_vec ? (S n) t1 (tape_move alpha (nth i ? t1 (niltape ?)) D) i.
   
lemma sem_move_multi :
  ∀alpha,n,i,D.i ≤ n → 
  mmove i alpha n D ⊨ Rm_multi alpha n i D.
#alpha #n #i #D #Hin #int %{2}
%{(mk_mconfig ? mmove_states n mmove1 ?)} 
[| %
 [ whd in ⊢ (??%?); @eq_f whd in ⊢ (??%?); @eq_f %
 | whd >tape_move_multi_def
   <(change_vec_same … (ctapes …) i (niltape ?))
   >pmap_change <tape_move_multi_def >tape_move_null_action % ] ]
 qed.
  
definition rewind ≝ λsrc,dst,sig,n.
  parmove src dst sig n L · mmove src sig n R · mmove dst sig n R.

definition R_rewind ≝ λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  (∀x,x0,xs,rs.
    nth src ? int (niltape ?) = midtape sig (xs@[x0]) x rs → 
    ∀ls0,y,y0,target,rs0.|xs| = |target| → 
    nth dst ? int (niltape ?) = midtape sig (target@y0::ls0) y rs0 → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig [] x0 (reverse ? xs@x::rs)) src)
           (midtape sig ls0 y0 (reverse ? target@y::rs0)) dst) ∧
  (∀x,rs.nth src ? int (niltape ?) = midtape sig [] x rs → 
   ∀ls0,y,rs0.nth dst ? int (niltape ?) = midtape sig ls0 y rs0 → 
   outt = int).

(*
theorem accRealize_to_Realize :
  ∀sig,n.∀M:mTM sig n.∀Rtrue,Rfalse,acc.
  M ⊨ [ acc: Rtrue, Rfalse ] →  M ⊨ Rtrue ∪ Rfalse.
#sig #n #M #Rtrue #Rfalse #acc #HR #t
cases (HR t) #k * #outc * * #Hloop
#Htrue #Hfalse %{k} %{outc} % // 
cases (true_or_false (cstate sig (states sig n M) n outc == acc)) #Hcase
[ % @Htrue @(\P Hcase) | %2 @Hfalse @(\Pf Hcase) ]
qed.
*)

lemma sem_rewind : ∀src,dst,sig,n.
  src ≠ dst → src < S n → dst < S n → 
  rewind src dst sig n ⊨ R_rewind src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst
@(sem_seq_app sig n ????? (sem_parmoveL src dst sig n Hneq Hsrc Hdst) ?)
[| @(sem_seq_app sig n ????? (sem_move_multi … R ?) (sem_move_multi … R ?)) //
 @le_S_S_to_le // ]
#ta #tb * #tc * * #Htc #_ * #td * whd in ⊢ (%→%→?); #Htd #Htb %
[ #x #x0 #xs #rs #Hmidta_src #ls0 #y #y0 #target #rs0 #Hlen #Hmidta_dst
  >(Htc ??? Hmidta_src ls0 y (target@[y0]) rs0 ??) in Htd;
  [|>Hmidta_dst //
  |>length_append >length_append >Hlen % ]
  >change_vec_commute [|@sym_not_eq //]
  >change_vec_change_vec
  >nth_change_vec_neq [|@sym_not_eq //]
  >nth_change_vec // >reverse_append >reverse_single
  >reverse_append >reverse_single normalize in match (tape_move ???);
  >rev_append_def >append_nil #Htd >Htd in Htb;
  >change_vec_change_vec >nth_change_vec //
  cases ls0 [|#l1 #ls1] normalize in match (tape_move ???); //
| #x #rs #Hmidta_src #ls0 #y #rs0 #Hmidta_dst
  lapply (Htc … Hmidta_src … (refl ??) Hmidta_dst) -Htc #Htc >Htc in Htd;
  >change_vec_commute [|@sym_not_eq //] >change_vec_change_vec
  >nth_change_vec_neq [|@sym_not_eq //] 
  >nth_change_vec // lapply (refl ? ls0) cases ls0 in ⊢ (???%→%);
  [ #Hls0 #Htd >Htd in Htb; 
    >nth_change_vec // >change_vec_change_vec 
    whd in match (tape_move ???);whd in match (tape_move ???); <Hmidta_src
    <Hls0 <Hmidta_dst >change_vec_same >change_vec_same //
  | #l1 #ls1 #Hls0 #Htd >Htd in Htb;
    >nth_change_vec // >change_vec_change_vec 
    whd in match (tape_move ???);whd in match (tape_move ???); <Hmidta_src
    <Hls0 <Hmidta_dst >change_vec_same >change_vec_same //
]]
qed.

definition match_step ≝ λsrc,dst,sig,n.
  compare src dst sig n ·
     (ifTM ?? (partest sig n (match_test src dst sig ?))
      (single_finalTM ??
        (rewind src dst sig n · (inject_TM ? (move_r ?) n dst)))
      (nop …)
      partest1).

(* we assume the src is a midtape
   we stop
   if the dst is out of bounds (outt = int)
   or dst.right is shorter than src.right (outt.current → None)
   or src.right is a prefix of dst.right (out = just right of the common prefix) *)
definition R_match_step_false ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ∀ls,x,xs.
  nth src ? int (niltape ?) = midtape sig ls x xs →
  ((current sig (nth dst (tape sig) int (niltape sig)) = None ?) ∧ outt = int) ∨
    (∃ls0,rs0,xs0. nth dst ? int (niltape ?) = midtape sig ls0 x rs0 ∧
      xs = rs0@xs0 ∧
      outt = change_vec ??
             (change_vec ?? int (mk_tape sig (reverse ? rs0@x::ls) (option_hd ? xs0) (tail ? xs0)) src)
             (mk_tape ? (reverse ? rs0@x::ls0) (None ?) [ ]) dst) ∨
    (∃ls0,rs0. 
     nth dst ? int (niltape ?) = midtape sig ls0 x (xs@rs0) ∧
     (* ∀rsj,c. 
     rs0 = c::rsj → *)
     outt = change_vec ??
            (change_vec ?? int (mk_tape sig (reverse ? xs@x::ls) (None ?) [ ]) src)
            (mk_tape sig (reverse ? xs@x::ls0) (option_hd ? rs0) (tail ? rs0)) dst).

(*
   we assume the src is a midtape [ ] s rs
   if we iterate
   then dst.current = Some ? s1
   and  if s ≠ s1 then outt = int.dst.move_right()
   and  if s = s1 
        then int.src.right and int.dst.right have a common prefix
        and  the heads of their suffixes are different
        and  outt = int.dst.move_right().
               
 *)
definition R_match_step_true ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ∀s,rs.nth src ? int (niltape ?) = midtape ? [ ] s rs → 
  outt = change_vec ?? int 
         (tape_move_mono … (nth dst ? int (niltape ?)) (〈None ?,R〉)) dst ∧
  (current sig (nth dst (tape sig) int (niltape sig)) = Some ? s → 
   ∃xs,ci,rs',ls0,cj,rs0.
   rs = xs@ci::rs' ∧
   nth dst ? int (niltape ?) = midtape sig ls0 s (xs@cj::rs0) ∧
   ci ≠ cj).
  
axiom daemon : ∀X:Prop.X.
      
lemma sem_match_step :
  ∀src,dst,sig,n.src ≠ dst → src < S n → dst < S n → 
  match_step src dst sig n ⊨ 
    [ inr ?? (inr ?? (inl … (inr ?? start_nop))) : 
      R_match_step_true src dst sig n, 
      R_match_step_false src dst sig n ].
#src #dst #sig #n #Hneq #Hsrc #Hdst 
@(acc_sem_seq_app sig n … (sem_compare src dst sig n Hneq Hsrc Hdst)
    (acc_sem_if ? n … (sem_partest sig n (match_test src dst sig ?))
      (sem_seq … 
        (sem_rewind ???? Hneq Hsrc Hdst) 
        (sem_inject … dst (le_S_S_to_le … Hdst) (sem_move_r ? )))
      (sem_nop …)))
[ #ta #tb #tc * lapply (refl ? (current ? (nth src ? ta (niltape ?))))
  cases (current ? (nth src ? ta (niltape ?))) in ⊢ (???%→%);
  [ #Hcurta_src #Hcomp #_ * #td * >Hcomp [| % %2 %]
    whd in ⊢ (%→?); * whd in ⊢ (??%?→?); 
    >nth_current_chars >Hcurta_src normalize in ⊢ (%→?); #H destruct (H)
  | #s #Hs lapply (refl ? (current ? (nth dst ? ta (niltape ?))))
    cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→%);
    [ #Hcurta_dst #Hcomp #_ * #td * >Hcomp [| %2 %]
      whd in ⊢ (%→?); * whd in ⊢ (??%?→?); 
      >nth_current_chars >nth_current_chars >Hs >Hcurta_dst 
      normalize in ⊢ (%→?); #H destruct (H)
    | #s0 #Hs0
      cases (current_to_midtape … Hs) #ls * #rs #Hmidta_src >Hmidta_src
      cases (current_to_midtape … Hs0) #ls0 * #rs0 #Hmidta_dst >Hmidta_dst
      cases (true_or_false (s == s0)) #Hss0
      [ lapply (\P Hss0) -Hss0 #Hss0 destruct (Hss0) 
        #_ #Hcomp cases (Hcomp ????? (refl ??) (refl ??)) -Hcomp [ *
        [ * #rs' * #_ #Hcurtc_dst * #td * whd in ⊢ (%→?); * whd in ⊢ (??%?→?);
          >nth_current_chars >nth_current_chars >Hcurtc_dst 
          cases (current ? (nth src …)) 
          [normalize in ⊢ (%→?); #H destruct (H)
          | #x >nth_change_vec // cases (reverse ? rs0)
            [ normalize in ⊢ (%→?); #H destruct (H)
            | #r1 #rs1 normalize in ⊢ (%→?); #H destruct (H) ] ]
        | * #rs0' * #_ #Hcurtc_src * #td * whd in ⊢ (%→?); * whd in ⊢ (??%?→?);
          >(?:nth src ? (current_chars ?? tc) (None ?) = None ?) 
          [|>nth_current_chars >Hcurtc_src >nth_change_vec_neq 
            [>nth_change_vec [cases (append ???) // | @Hsrc] 
            |@(not_to_not … Hneq) //
            ]]
          normalize in ⊢ (%→?); #H destruct (H) ]
        | * #xs * #ci * #cj * #rs'' * #rs0' * * * #Hcicj #Hrs #Hrs0
          #Htc * #td * * #Hmatch #Htd destruct (Htd) * #te * *
          >Htc >change_vec_commute // >nth_change_vec //
          >change_vec_commute [|@sym_not_eq //] >nth_change_vec // #Hte #_ #Htb
          #s' #rs' >Hmidta_src #H destruct (H)
          lapply (Hte … (refl ??) … (refl ??) (refl ??)) -Hte
          >change_vec_commute // >change_vec_change_vec
          >change_vec_commute [|@sym_not_eq //] >change_vec_change_vec #Hte
          >Hte in Htb; * * #_ >nth_change_vec // #Htb1
          lapply (Htb1 … (refl ??)) -Htb1 #Htb1 #Htb2 %
          [ @(eq_vec … (niltape ?)) #i #Hi
            cases (true_or_false ((dst : DeqNat) == i)) #Hdsti
            [ <(\P Hdsti) >Htb1 >nth_change_vec // >Hmidta_dst
              >Hrs0 >reverse_reverse cases xs [|#r1 #rs1] %
            | <Htb2 [|@(\Pf Hdsti)] >nth_change_vec_neq [| @(\Pf Hdsti)]
              >Hrs0 >reverse_reverse >nth_change_vec_neq in ⊢ (???%); 
              <Hrs <Hmidta_src [|@(\Pf Hdsti)] >change_vec_same % ]
          | #_ >Hmidta_dst >Hrs0
            %{xs} %{ci} %{rs''} %{ls0} %{cj} %{rs0'} % // % // 
          ]
        ]
      | lapply (\Pf Hss0) -Hss0 #Hss0 #Htc cut (tc = ta) 
        [@Htc % % @(not_to_not ??? Hss0) #H destruct (H) %]
        -Htc #Htc destruct (Htc) #_ * #td * whd in ⊢ (%→?); * #_ 
        #Htd destruct (Htd) * #te * * #_ #Hte * * #_ #Htb1 #Htb2
        #s1 #rs1 >Hmidta_src #H destruct (H)
        lapply (Hte … Hmidta_src … Hmidta_dst) -Hte #Hte destruct (Hte) %
        [ @(eq_vec … (niltape ?)) #i #Hi
          cases (true_or_false ((dst : DeqNat) == i)) #Hdsti
          [ <(\P Hdsti) >(Htb1 … Hmidta_dst) >nth_change_vec // >Hmidta_dst
            cases rs0 [|#r2 #rs2] %
          | <Htb2 [|@(\Pf Hdsti)] >nth_change_vec_neq [| @(\Pf Hdsti)] % ]
        | >Hs0 #H destruct (H) @False_ind cases (Hss0) /2/ ]
      ]
    ]
  ]
| #ta #tb #tc * #Hcomp1 #Hcomp2 * #td * * #Htest #Htd destruct (Htd)
  whd in ⊢ (%→?); #Htb destruct (Htb) #ls #x #xs #Hta_src
  lapply (refl ? (current ? (nth dst ? ta (niltape ?))))
  cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→?);
  [ #Hcurta_dst % % % // @Hcomp1 %2 //
  | #x0 #Hcurta_dst cases (current_to_midtape … Hcurta_dst) -Hcurta_dst
    #ls0 * #rs0 #Hta_dst cases (true_or_false (x == x0)) #Hxx0
    [ lapply (\P Hxx0) -Hxx0 #Hxx0 destruct (Hxx0)
    | >(?:tc=ta) in Htest; 
      [|@Hcomp1 % % >Hta_src >Hta_dst @(not_to_not ??? (\Pf Hxx0)) normalize
        #Hxx0' destruct (Hxx0') % ]
      whd in ⊢ (??%?→?); 
      >nth_current_chars >Hta_src >nth_current_chars >Hta_dst 
      whd in ⊢ (??%?→?); #Hfalse destruct (Hfalse) ] -Hcomp1
      cases (Hcomp2 … Hta_src Hta_dst) [ *
      [ * #rs' * #Hxs #Hcurtc % %2 %{ls0} %{rs0} %{rs'} %
        [ % // | >Hcurtc % ]
      | * #rs0' * #Hxs #Htc %2 >Htc %{ls0} %{rs0'} % // ]
      | * #xs0 * #ci * #cj * #rs' * #rs0' * * *
        #Hci #Hxs #Hrs0 #Htc @False_ind
        whd in Htest:(??%?); 
        >(?:nth src ? (current_chars ?? tc) (None ?) = Some ? ci) in Htest; 
        [|>nth_current_chars >Htc >nth_change_vec_neq [|@(not_to_not … Hneq) //]
          >nth_change_vec //]
        >(?:nth dst ? (current_chars ?? tc) (None ?) = Some ? cj) 
        [|>nth_current_chars >Htc >nth_change_vec //]
        normalize #H destruct (H) ] ] ]
qed.

definition match_m ≝ λsrc,dst,sig,n.
  whileTM … (match_step src dst sig n) 
    (inr ?? (inr ?? (inl … (inr ?? start_nop)))).

definition R_match_m ≝ 
  λsrc,dst,sig,n.λint,outt: Vector (tape sig) (S n).
  ∀x,rs.
  nth src ? int (niltape ?) = midtape sig [ ] x rs →
  (current sig (nth dst (tape sig) int (niltape sig)) = None ? → outt = int) ∧
  (∀ls0,x0,rs0.
   nth dst ? int (niltape ?) = midtape sig ls0 x0 rs0 →
   (∃l,l1.x0::rs0 = l@x::rs@l1 ∧
    outt = change_vec ?? 
           (change_vec ?? int 
             (mk_tape sig (reverse ? rs@[x]) (None ?) [ ]) src)
           (mk_tape sig ((reverse ? (l@x::rs))@ls0) (option_hd ? l1) (tail ? l1)) dst) ∨
    ∀l,l1.x0::rs0 ≠ l@x::rs@l1).

lemma not_sub_list_merge : 
  ∀T.∀a,b:list T. (∀l1.a ≠ b@l1) → (∀t,l,l1.a ≠ t::l@b@l1) → ∀l,l1.a ≠ l@b@l1.
#T #a #b #H1 #H2 #l elim l normalize //
qed.

lemma not_sub_list_merge_2 : 
  ∀T:DeqSet.∀a,b:list T.∀t. (∀l1.t::a ≠ b@l1) → (∀l,l1.a ≠ l@b@l1) → ∀l,l1.t::a ≠ l@b@l1.
#T #a #b #t #H1 #H2 #l elim l //
#t0 #l1 #IH #l2 cases (true_or_false (t == t0)) #Htt0
[ >(\P Htt0) % normalize #H destruct (H) cases (H2 l1 l2) /2/
| normalize % #H destruct (H) cases (\Pf Htt0) /2/ ]
qed.


lemma wsem_match_m : ∀src,dst,sig,n.
src ≠ dst → src < S n → dst < S n → 
  match_m src dst sig n ⊫ R_match_m src dst sig n.
#src #dst #sig #n #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_match_step src dst sig n Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ #Hfalse #x #xs #Hmid_src
  cases (Hfalse … Hmid_src) -Hfalse 
  [(* current dest = None *) *
    [ * #Hcur_dst #Houtc %
      [#_ >Houtc //
      | #ls0 #x0 #rs0 #Hmid_dst >Hmid_dst in Hcur_dst; 
        normalize in ⊢ (%→?); #H destruct (H)
      ]
    | * #ls0 * #rs0 * #xs0 * * #Htc_dst #Hrs0 #HNone %
      [ >Htc_dst normalize in ⊢ (%→?); #H destruct (H)
      | #ls1 #x1 #rs1 >Htc_dst #H destruct (H)
        >Hrs0 >HNone cases xs0
        [ % %{[ ]} %{[ ]} % [ >append_nil >append_nil %]
          @eq_f3 //
          [ >reverse_append %
          | >reverse_append >reverse_cons >reverse_append
            >associative_append >associative_append % ]
        | #x2 #xs2 %2 #l #l1 % #Habs lapply (eq_f ?? (length ?) ?? Habs)
          >length_append whd in ⊢ (??%(??%)→?); >length_append
          >length_append normalize >commutative_plus whd in ⊢ (???%→?);
          #H destruct (H) lapply e0 >(plus_n_O (|rs1|)) in ⊢ (??%?→?);
          >associative_plus >associative_plus 
          #e1 lapply (injective_plus_r ??? e1) whd in ⊢ (???%→?);
          #e2 destruct (e2)
        ]
      ]
    ]
  |* #ls0 * #rs0 * #Hmid_dst #Houtc %
    [ >Hmid_dst normalize in ⊢ (%→?); #H destruct (H)
    |#ls1 #x1 #rs1 >Hmid_dst #H destruct (H)
     %1 %{[ ]} %{rs0} % [%] 
     >reverse_cons >associative_append >Houtc %
    ]
  ]
|-ta #ta #tc #Htrue #Hstar #IH #Hout lapply (IH Hout) -IH -Hout #IH whd
 #x #xs #Hmidta_src
 lapply (refl ? (current ? (nth dst ? ta (niltape ?))))
 cases (current ? (nth dst ? ta (niltape ?))) in ⊢ (???%→?); 
  [#Hcurta_dst % 
    [#_ whd in Htrue; >Hmidta_src in Htrue; #Htrue
     cases (Htrue ?? (refl ??)) -Htrue >Hcurta_dst
     (* dovremmo sapere che ta.dst è sul margine destro, da cui la move non 
        ha effetto *) #_ cut (tc = ta) [@daemon] #Htc destruct (Htc) #_
     cases (IH … Hmidta_src) #Houtc #_ @Houtc //
    |#ls0 #x0 #rs0 #Hmidta_dst >Hmidta_dst in Hcurta_dst;
     normalize in ⊢ (%→?); #H destruct (H)
    ]
  | #c #Hcurta_dst % [ >Hcurta_dst #H destruct (H) ]
    #ls0 #x0 #rs0 #Hmidta_dst >Hmidta_dst in Hcurta_dst; normalize in ⊢ (%→?);
    #H destruct (H) whd in Htrue; >Hmidta_src in Htrue; #Htrue
    cases (Htrue ?? (refl …)) -Htrue >Hmidta_dst #Htc
    cases (true_or_false (x==c)) #eqx
    [ lapply (\P eqx) -eqx #eqx destruct (eqx)
      #Htrue cases (Htrue (refl ??)) -Htrue
      #xs0 * #ci * #rs' * #ls1 * #cj * #rs1 * * #Hxs #H destruct (H) #Hcicj
      >Htc in IH; whd in ⊢ (%→?); >nth_change_vec_neq [|@sym_not_eq //]
      #IH cases (IH … Hmidta_src) -IH #_ >nth_change_vec //
      cut (∃x1,xs1.xs0@cj::rs1 = x1::xs1)
      [ cases xs0 [ %{cj} %{rs1} % | #x1 #xs1 %{x1} %{(xs1@cj::rs1)} % ] ] * #x1 * #xs1
      #Hxs1 >Hxs1 #IH cases (IH … (refl ??)) -IH
      [ * #l * #l1 * #Hxs1'
        >change_vec_commute // >change_vec_change_vec
        #Houtc % %{(c::l)} %{l1} % 
        [ normalize <Hxs1' %
        | >reverse_cons >associative_append >change_vec_commute // @Houtc ]
      | #H %2 #l #l1 >(?:l@c::xs@l1 = l@(c::xs)@l1) [|%]
        @not_sub_list_merge
        [ #l2 >Hxs <Hxs1 % normalize #H1 lapply (cons_injective_r ????? H1)
          >associative_append #H2 lapply (append_l2_injective ????? (refl ??) H2)
          #H3 lapply (cons_injective_l ????? H3) #H3 >H3 in Hcicj; * /2/
        |#t #l2 #l3 % normalize #H1 lapply (cons_injective_r ????? H1)
         -H1 #H1 cases (H l2 l3) #H2 @H2 @H1
        ]
      ]
    | #_ cases (IH x xs ?) -IH
      [| >Htc >nth_change_vec_neq [|@sym_not_eq //] @Hmidta_src ]
      >Htc >nth_change_vec // cases rs0
      [ #_ #_ %2 #l #l1 cases l
       [ normalize cases xs
         [ cases l1
           [ normalize % #H destruct (H) cases (\Pf eqx) /2/
           | #tmp1 #l2 normalize % #H destruct (H) ]
         | #tmp1 #l2 normalize % #H destruct (H) ]
       | #tmp1 #l2 normalize % #H destruct (H)cases l2 in e0;
         [ normalize #H1 destruct (H1)
         | #tmp2 #l3 normalize #H1 destruct (H1) ] ]
      | #r1 #rs1 #_ #IH cases (IH … (refl ??)) -IH
        [ * #l * #l1 * #Hll1 #Houtc % %{(c::l)} %{l1} % [ >Hll1 % ]
          >Houtc >change_vec_commute // >change_vec_change_vec 
          >change_vec_commute [|@sym_not_eq //]
          >reverse_cons >associative_append %
        | #Hll1 %2 @(not_sub_list_merge_2 ?? (x::xs)) normalize [|@Hll1]
         #l1 % #H destruct (H) cases (\Pf eqx) /2/
        ]
      ]
    ]
  ]
]
qed.

definition Pre_match_m ≝ 
  λsrc,sig,n.λt: Vector (tape sig) (S n).
  ∃x,xs.
  nth src (tape sig) t (niltape sig) = midtape ? [] x xs.
  
lemma terminate_match_m :
  ∀src,dst,sig,n,t.
  src ≠ dst → src < S n → dst < S n → 
  Pre_match_m src sig n t → 
  match_m src dst sig n ↓ t.
#src #dst #sig #n #t #Hneq #Hsrc #Hdst * #start * #xs
#Hmid_src
@(terminate_while … (sem_match_step src dst sig n Hneq Hsrc Hdst)) //
<(change_vec_same … t dst (niltape ?))
lapply (refl ? (nth dst (tape sig) t (niltape ?))) 
cases (nth dst (tape sig) t (niltape ?)) in ⊢ (???%→?);
[ #Htape_dst % #t1 whd in ⊢ (%→?); >nth_change_vec_neq [|@sym_not_eq //]
  >Hmid_src #HR cases (HR ?? (refl ??)) -HR
  >nth_change_vec // >Htape_dst
| #x0 #xs0 #Htape_dst % #t1 whd in ⊢ (%→?); >nth_change_vec_neq [|@sym_not_eq //]
  >Hmid_src #HR cases (HR ? (refl ??)) -HR
  >nth_change_vec // >Htape_dst normalize in ⊢ (%→?);
  * #H @False_ind @H %
| #x0 #xs0 #Htape_dst % #t1 whd in ⊢ (%→?); >nth_change_vec_neq [|@sym_not_eq //]
  >Hmid_src #HR cases (HR ? (refl ??)) -HR
  >nth_change_vec // >Htape_dst normalize in ⊢ (%→?);
  * #H @False_ind @H %
| #ls #s #rs lapply s -s lapply ls -ls lapply Hmid_src lapply t -t elim rs
  [#t #Hmid_src #ls #s #Hmid_dst % #t1 whd in ⊢ (%→?); >nth_change_vec_neq [|@sym_not_eq //]
   >Hmid_src >nth_change_vec // >Hmid_dst #HR cases (HR ? (refl ??)) -HR #_
   #HR cases (HR Hstart Hnotstart)
   cases (true_or_false (start == s)) #Hs
   [ lapply (\P Hs) -Hs #Hs <Hs #_ #Htrue
     cut (∃ci,xs1.xs@[end] = ci::xs1)
     [ cases xs
       [ %{end} %{[]} %
       | #x1 #xs1 %{x1} %{(xs1@[end])} % ] ] * #ci * #xs1 #Hxs
     >Hxs in Htrue; #Htrue
     cases (Htrue [ ] start [ ] ? xs1 ? [ ] (refl ??) (refl ??) ?)
     [ * #_ * #H @False_ind @H % ]
     #c0 #Hc0 @Hnotend >(memb_single … Hc0) @memb_hd
   | lapply (\Pf Hs) -Hs #Hs #Htrue #_
     cases (Htrue ? (refl ??) Hs) -Htrue #Ht1 #_ %
     #t2 whd in ⊢ (%→?); #HR cases (HR start ?)
     [ >Ht1 >nth_change_vec // normalize in ⊢ (%→?); * #H @False_ind @H %
     | >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
       >nth_change_vec_neq [|@sym_not_eq //] >Hmid_src % ]
   ]
  |#r0 #rs0 #IH #t #Hmid_src #ls #s #Hmid_dst % #t1 whd in ⊢ (%→?);
   >nth_change_vec_neq [|@sym_not_eq //] >Hmid_src
   #Htrue cases (Htrue ? (refl ??)) -Htrue #_ #Htrue
   <(change_vec_same … t1 dst (niltape ?))
   cases (Htrue Hstart Hnotstart) -Htrue
   cases (true_or_false (start == s)) #Hs
   [ lapply (\P Hs) -Hs #Hs <Hs #_ #Htrue
    cut (∃ls0,xs0,ci,rs,rs0.
      nth src ? t (niltape ?) = midtape sig [ ] start (xs0@ci::rs) ∧
      nth dst ? t (niltape ?) = midtape sig ls0 s (xs0@rs0) ∧
      (is_endc ci = true ∨ (is_endc ci = false ∧ (∀b,tlb.rs0 = b::tlb → ci ≠ b))))
    [cases (comp_list ? (xs@[end]) (r0::rs0) is_endc) #xs0 * #xs1 * #xs2
      * * * #Hxs #Hrs #Hxs0notend #Hcomp >Hrs
      cut (∃y,ys. xs1 = y::ys)
      [ lapply Hxs0notend lapply Hxs lapply xs0 elim xs
        [ *
          [ normalize #Hxs1 <Hxs1 #_ %{end} %{[]} %
          | #z #zs normalize in ⊢ (%→?); #H destruct (H) #H
            lapply (H ? (memb_hd …)) -H >Hend #H1 destruct (H1)
          ]
        | #y #ys #IH0 * 
          [ normalize in ⊢ (%→?); #Hxs1 <Hxs1 #_ %{y} %{(ys@[end])} %
          | #z #zs normalize in ⊢ (%→?); #H destruct (H) #Hmemb
            @(IH0 ? e0 ?) #c #Hc @Hmemb @memb_cons // ] ] ] * #y * #ys #Hxs1
      >Hxs1 in Hxs; #Hxs >Hmid_src >Hmid_dst >Hxs >Hrs
      %{ls} %{xs0} %{y} %{ys} %{xs2}
      % [ % // | @Hcomp // ] ]
    * #ls0 * #xs0 * #ci * #rs * #rs0 * * #Hmid_src' #Hmid_dst' #Hcomp
    <Hmid_src in Htrue; >nth_change_vec // >Hs #Htrue destruct (Hs)
    lapply (Htrue ??????? Hmid_src' Hmid_dst' ?) -Htrue
    [ #c0 #Hc0 @Hnotend cases (orb_true_l … Hc0) -Hc0 #Hc0
      [ whd in ⊢ (??%?); >Hc0 %
      | @memb_cons >Hmid_src in Hmid_src'; #Hmid_src' destruct (Hmid_src')
        lapply e0 -e0 @(list_elim_left … rs)
        [ #e0 destruct (e0) lapply (append_l1_injective_r ?????? e0) //
        | #x1 #xs1 #_ >append_cons in ⊢ (???%→?);
          <associative_append #e0 lapply (append_l1_injective_r ?????? e0) //
          #e1 >e1 @memb_append_l1 @memb_append_l1 // ] ]
    | * * #Hciendc cases rs0 in Hcomp;
      [ #_ * #H @False_ind @H %
      | #r1 #rs1 * [ >Hciendc #H destruct (H) ]
        * #_ #Hcomp lapply (Hcomp ?? (refl ??)) -Hcomp #Hcomp #_ #Htrue
        cases (Htrue ?? (refl ??) Hcomp) #Ht1 #_ >Ht1 @(IH ?? (s::ls) r0)
        [ >nth_change_vec_neq [|@sym_not_eq //]
          >nth_change_vec_neq [|@sym_not_eq //] @Hmid_src
        | >nth_change_vec // >Hmid_dst % ] ] ]
  | >Hmid_dst >nth_change_vec // lapply (\Pf Hs) -Hs #Hs #Htrue #_
    cases (Htrue ? (refl ??) Hs) #Ht1 #_ >Ht1 @(IH ?? (s::ls) r0)
    [ >nth_change_vec_neq [|@sym_not_eq //]
      >nth_change_vec_neq [|@sym_not_eq //] @Hmid_src
    | >nth_change_vec // ] ] ] ]
qed.