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

include "turing/turing.ma".
include "turing/inject.ma".
include "turing/while_multi.ma".

definition copy_states ≝ initN 3.

definition copy0 : copy_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition copy1 : copy_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition copy2 : copy_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

(*

src: a b c ... z # ---→ a b c ... z #
     ^                              ^

dst: _ _ _ ... _ d ---→ a b c ... z d
     ^                              ^

0) (x ≠ sep,_) → (x,x)(R,R) → 1
   (sep,d) → None 2
1) (_,_) → None 1
2) (_,_) → None 2

*)

definition trans_copy_step ≝ 
 λsrc,dst,sig,n,is_sep.
 λp:copy_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth src ? a (None ?) with
   [ None ⇒ 〈copy2,null_action ? n〉
   | Some a0 ⇒ if is_sep a0 then 〈copy2,null_action ? n〉
                  else 〈copy1,change_vec ? (S n)
                          (change_vec ?(S n)
                           (null_action ? n) (Some ? 〈a0,R〉) src)
                          (Some ? 〈a0,R〉) dst〉 ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈copy1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈copy2,null_action ? n〉 ] ].

definition copy_step ≝ 
  λsrc,dst,sig,n,is_sep.
  mk_mTM sig n copy_states (trans_copy_step src dst sig n is_sep) 
    copy0 (λq.q == copy1 ∨ q == copy2).

definition R_copy_step_true ≝ 
  λsrc,dst,sig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  ∃x1.
   current ? (nth src ? int (niltape ?)) = Some ? x1 ∧
   is_sep x1 = false ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move ? (nth src ? int (niltape ?)) (Some ? 〈x1,R〉)) src)
            (tape_move ? (nth dst ? int (niltape ?)) (Some ? 〈x1,R〉)) dst.

definition R_copy_step_false ≝ 
  λsrc,dst:nat.λsig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  (∃x1.
   current ? (nth src ? int (niltape ?)) = Some ? x1 ∧
   is_sep x1 = true ∧ outt = int) ∨
   current ? (nth src ? int (niltape ?)) = None ? ∧
   outt = int.

lemma copy_q0_q2_null :
  ∀src,dst,sig,n,is_sep,v,t.src < S n → dst < S n → 
  current ? t = None ? → 
  step sig n (copy_step src dst sig n is_sep)
    (mk_mconfig ??? copy0 (change_vec ? (S n) v t src)) =
    mk_mconfig ??? copy2 (change_vec ? (S n) v t src).
#src #dst #sig #n #is_sep #v #t #Hsrc #Hdst #Hcurrent
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent %
| >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent @tape_move_null_action
]
qed.

lemma copy_q0_q2_sep :
  ∀src,dst,sig,n,is_sep,v,t.src < S n → dst < S n → 
  ∀s.current ? t = Some ? s → is_sep s = true → 
  step sig n (copy_step src dst sig n is_sep)
    (mk_mconfig ??? copy0 (change_vec ? (S n) v t src)) =
    mk_mconfig ??? copy2 (change_vec ? (S n) v t src).
#src #dst #sig #n #is_sep #v #t #Hsrc #Hdst #s #Hcurrent #Hsep
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???%)?); >Hsep %
| >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???????(???%))?);
  >Hsep @tape_move_null_action
]
qed.

lemma copy_q0_q1 :
  ∀src,dst,sig,n,is_sep,v,t.src ≠ dst → src < S n → dst < S n → 
  ∀s.current ? t = Some ? s → is_sep s = false → 
  step sig n (copy_step src dst sig n is_sep)
    (mk_mconfig ??? copy0 (change_vec ? (S n) v t src)) =
    mk_mconfig ??? copy1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? t (Some ? 〈s,R〉)) src)
       (tape_move ? (nth dst ? v (niltape ?)) (Some ? 〈s,R〉)) dst).
#src #dst #sig #n #is_sep #v #t #Hneq #Hsrc #Hdst #s #Hcurrent #Hsep
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???%)?); >Hsep %
| >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???????(???%))?);
  >Hsep whd in ⊢ (??(???????(???%))?); >change_vec_commute // >pmap_change
  >change_vec_commute // @eq_f3 //
  <(change_vec_same ?? v dst (niltape ?)) in ⊢(??%?);
  >pmap_change @eq_f3 //
]
qed.

lemma sem_copy_step :
  ∀src,dst,sig,n,is_sep.src ≠ dst → src < S n → dst < S n → 
  copy_step src dst sig n is_sep ⊨ 
    [ copy1: R_copy_step_true src dst sig n is_sep, 
             R_copy_step_false src dst sig n is_sep ].
#src #dst #sig #n #is_sep #Hneq #Hsrc #Hdst #int
lapply (refl ? (current ? (nth src ? int (niltape ?))))
cases (current ? (nth src ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcur <(change_vec_same … int src (niltape ?)) %{2} %
  [| % [ % 
    [ whd in ⊢ (??%?); >copy_q0_q2_null /2/ 
    | normalize in ⊢ (%→?); #H destruct (H) ]
    | #_ %2 >nth_change_vec >Hcur // % // ] ]
| #c #Hcur cases (true_or_false (is_sep c)) #Hsep
  [ <(change_vec_same … int src (niltape ?)) %{2} % 
    [| % [ %
      [ whd in ⊢ (??%?); >copy_q0_q2_sep /2/
      | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % >nth_change_vec // %{c} % [ % /2/ | // ] ] ]
  | %{2} % [| % [ %
    [ whd in ⊢ (??%?);
      <(change_vec_same … int src (niltape ?)) in ⊢ (??%?);
      >Hcur in ⊢ (??%?); whd in ⊢ (??%?); >(copy_q0_q1 … Hsep) /2/
    | #_ whd %{c} % % /2/ ]
    | * #Hfalse @False_ind /2/ ] ] ] ]
qed.

definition copy ≝ λsrc,dst,sig,n,is_sep.
  whileTM … (copy_step src dst sig n is_sep) copy1.

definition R_copy ≝ 
  λsrc,dst,sig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  (∀ls,x,xs,rs,sep.
    nth src ? int (niltape ?) = midtape sig ls x (xs@sep::rs) →
    (∀c.memb ? c (x::xs) = true → is_sep c = false) → is_sep sep = true → 
    ∀ls0,x0,target,c,rs0.|xs| = |target| → 
    nth dst ? int (niltape ?) = midtape sig ls0 x0 (target@c::rs0) → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig (reverse ? xs@x::ls) sep rs) src)
           (midtape sig (reverse ? xs@x::ls0) c rs0) dst) ∧
  (∀c.current ? (nth src ? int (niltape ?)) = Some ? c → is_sep c = true → 
   outt = int) ∧
  (current ? (nth src ? int (niltape ?)) = None ? → outt = int).
  
lemma wsem_copy : ∀src,dst,sig,n,is_sep.src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n is_sep ⊫ R_copy src dst sig n is_sep.
#src #dst #sig #n #is_sep #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_copy_step src dst sig n is_sep Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar -ta
[ whd in ⊢ (%→?); *
  [ * #x * * #Hx #Hsep #Houtc % [ %
    [ #ls #x0 #xs #rs #sep #Hsrctc #Hnosep >Hsrctc in Hx; normalize in ⊢ (%→?);
      #Hx0 destruct (Hx0) lapply (Hnosep ? (memb_hd …)) >Hsep
      #Hfalse destruct (Hfalse)
    | #c #Hc #Hsepc @Houtc ]
    | #_ @Houtc ]
  | * #Hcur #Houtc % [ %
    [ #ls #x0 #xs #rs #sep #Hsrctc >Hsrctc in Hcur; normalize in ⊢ (%→?); 
      #Hcur destruct (Hcur)
    | #c #Hc #Hsepc @Houtc ]
    | #_ @Houtc ]
  ]
| #td #te * #c0 * * #Hc0 #Hc0nosep #Hd #Hstar #IH #He 
  lapply (IH He) -IH * * #IH1 #IH2 #IH3 % [ %
  [ #ls #x #xs #rs #sep #Hsrc_tc #Hnosep #Hsep #ls0 #x0 #target
    #c #rs0 #Hlen #Hdst_tc
    >Hsrc_tc in Hc0; normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
    <(change_vec_same … td src (niltape ?)) in Hd:(???(???(???%??)??));
    <(change_vec_same … td dst (niltape ?)) in ⊢(???(???(???%??)??)→?);
    >Hdst_tc >Hsrc_tc >(change_vec_change_vec ?) >change_vec_change_vec
    >(change_vec_commute ?? td ?? dst src) [|@(sym_not_eq … Hneq)]
    >change_vec_change_vec @(list_cases2 … Hlen)
    [ #Hxsnil #Htargetnil #Hd>(IH2 … Hsep)
      [ >Hd -Hd >Hxsnil >Htargetnil @(eq_vec … (niltape ?))
        #i #Hi cases (decidable_eq_nat i src) #Hisrc
        [ >Hisrc >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
          >nth_change_vec // >nth_change_vec //
          >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
          >nth_change_vec // whd in ⊢ (??%?); %
        | cases (decidable_eq_nat i dst) #Hidst
          [ >Hidst >nth_change_vec // >nth_change_vec //
            >nth_change_vec_neq // >Hdst_tc >Htargetnil %
          | >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
            >nth_change_vec_neq [|@(sym_not_eq … Hisrc)]
            >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
            >nth_change_vec_neq [|@(sym_not_eq … Hisrc)] % ]
         ]
      | >Hd >nth_change_vec_neq [|@(sym_not_eq … Hneq)]
        >nth_change_vec // >nth_change_vec // >Hxsnil % ]
    |#hd1 #hd2 #tl1 #tl2 #Hxs #Htarget >Hxs >Htarget #Hd
     >(IH1 (c0::ls) hd1 tl1 rs sep ?? Hsep (c0::ls0) hd2 tl2 c rs0)
     [ >Hd >(change_vec_commute … ?? td ?? src dst) //
       >change_vec_change_vec
       >(change_vec_commute … ?? td ?? dst src) [|@sym_not_eq //]
       >change_vec_change_vec
       >reverse_cons >associative_append >associative_append % 
     | >Hd >nth_change_vec // >nth_change_vec_neq // >Hdst_tc >Htarget //
     | >Hxs in Hlen; >Htarget normalize #Hlen destruct (Hlen) //
     | <Hxs #c1 #Hc1 @Hnosep @memb_cons //
     | >Hd >nth_change_vec_neq [|@sym_not_eq //]
       >nth_change_vec // >nth_change_vec // ]
   ]
 | #c #Hc #Hsepc >Hc in Hc0; #Hcc0 destruct (Hcc0) >Hc0nosep in Hsepc;
   #H destruct (H)
 ]
| #HNone >HNone in Hc0; #Hc0 destruct (Hc0) ] ]
qed.
 
lemma terminate_copy :  ∀src,dst,sig,n,is_sep,t.
  src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n is_sep ↓ t.
#src #dst #sig #n #is_sep #t #Hneq #Hsrc #Hdst
@(terminate_while … (sem_copy_step …)) //
<(change_vec_same … t src (niltape ?))
cases (nth src (tape sig) t (niltape ?))
[ % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct 
|2,3: #a0 #al0 % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls #c #rs lapply c -c lapply ls -ls lapply t -t elim rs
  [#t #ls #c % #t1 * #x * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #Hxsep >change_vec_change_vec #Ht1 % 
   #t2 * #x0 * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#r0 #rs0 #IH #t #ls #c % #t1 * #x * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hxsep
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_copy : ∀src,dst,sig,n,is_sep.
  src ≠ dst → src < S n → dst < S n → 
  copy src dst sig n is_sep ⊨ R_copy src dst sig n is_sep.
#src #dst #sig #n #is_sep #Hneq #Hsrc #Hdst @WRealize_to_Realize /2/
qed.