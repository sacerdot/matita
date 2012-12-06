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

include "turing/turing.ma".
include "turing/inject.ma".
include "turing/while_multi.ma".

definition parmove_states ≝ initN 3.

definition parmove0 : parmove_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 3 (refl …)).
definition parmove1 : parmove_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 3 (refl …)).
definition parmove2 : parmove_states ≝ mk_Sig ?? 2 (leb_true_to_le 3 3 (refl …)).

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

definition trans_parmove_step ≝ 
 λsrc,dst,sig,n,D,is_sep.
 λp:parmove_states × (Vector (option sig) (S n)).
 let 〈q,a〉 ≝ p in
 match pi1 … q with
 [ O ⇒ match nth src ? a (None ?) with
   [ None ⇒ 〈parmove2,null_action ? n〉
   | Some a0 ⇒ 
     if is_sep a0 then 〈parmove2,null_action ? n〉
     else match nth dst ? a (None ?) with
     [ None ⇒ 〈parmove2,null_action ? n〉
     | Some a1 ⇒ 〈parmove1,change_vec ? (S n)
                          (change_vec ?(S n)
                           (null_action ? n) (Some ? 〈a0,D〉) src)
                          (Some ? 〈a1,D〉) dst〉 ] ]
 | S q ⇒ match q with 
   [ O ⇒ (* 1 *) 〈parmove1,null_action ? n〉
   | S _ ⇒ (* 2 *) 〈parmove2,null_action ? n〉 ] ].

definition parmove_step ≝ 
  λsrc,dst,sig,n,D,is_sep.
  mk_mTM sig n parmove_states (trans_parmove_step src dst sig n D is_sep) 
    parmove0 (λq.q == parmove1 ∨ q == parmove2).

definition R_parmove_step_true ≝ 
  λsrc,dst,sig,n,D,is_sep.λint,outt: Vector (tape sig) (S n).
  ∃x1,x2.
   current ? (nth src ? int (niltape ?)) = Some ? x1 ∧
   current ? (nth dst ? int (niltape ?)) = Some ? x2 ∧
   is_sep x1 = false ∧
   outt = change_vec ?? 
            (change_vec ?? int
              (tape_move ? (nth src ? int (niltape ?)) (Some ? 〈x1,D〉)) src)
            (tape_move ? (nth dst ? int (niltape ?)) (Some ? 〈x2,D〉)) dst.

definition R_parmove_step_false ≝ 
  λsrc,dst:nat.λsig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  ((∃x1.
   current ? (nth src ? int (niltape ?)) = Some ? x1 ∧
   is_sep x1 = true) ∨
   current ? (nth src ? int (niltape ?)) = None ?  ∨
   current ? (nth dst ? int (niltape ?)) = None ?) ∧
   outt = int.

lemma parmove_q0_q2_null_src :
  ∀src,dst,sig,n,D,is_sep,v.src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = None ? → 
  step sig n (parmove_step src dst sig n D is_sep)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove2 v.
#src #dst #sig #n #D #is_sep #v #Hsrc #Hdst #Hcurrent
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Hcurrent %
| whd in ⊢ (??(???????(???%))?); >Hcurrent @tape_move_null_action ]
qed.

lemma parmove_q0_q2_sep :
  ∀src,dst,sig,n,D,is_sep,v,s.src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = Some ? s → is_sep s = true → 
  step sig n (parmove_step src dst sig n D is_sep)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove2 v.
#src #dst #sig #n #D #is_sep #v #s #Hsrc #Hdst #Hcurrent #Hsep
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Hcurrent whd in ⊢ (??(???%)?); >Hsep %
| whd in ⊢ (??(???????(???%))?); >Hcurrent
  whd in ⊢ (??(???????(???%))?); >Hsep @tape_move_null_action ]
qed.

lemma parmove_q0_q2_null_dst :
  ∀src,dst,sig,n,D,is_sep,v,s.src < S n → dst < S n → 
  nth src ? (current_chars ?? v) (None ?) = Some ? s → is_sep s = false → 
  nth dst ? (current_chars ?? v) (None ?) = None ? → 
  step sig n (parmove_step src dst sig n D is_sep)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove2 v.
#src #dst #sig #n #D #is_sep #v #s #Hsrc #Hdst #Hcursrc #Hsep #Hcurdst
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?);
@eq_f2
[ whd in ⊢ (??(???%)?); >Hcursrc whd in ⊢ (??(???%)?); >Hsep >Hcurdst %
| whd in ⊢ (??(???????(???%))?); >Hcursrc
  whd in ⊢ (??(???????(???%))?); >Hsep >Hcurdst @tape_move_null_action ]
qed.

lemma parmove_q0_q1 :
  ∀src,dst,sig,n,D,is_sep,v.src ≠ dst → src < S n → dst < S n → 
  ∀a1,a2.
  nth src ? (current_chars ?? v) (None ?) = Some ? a1 →
  nth dst ? (current_chars ?? v) (None ?) = Some ? a2 → 
  is_sep a1 = false → 
  step sig n (parmove_step src dst sig n D is_sep)
    (mk_mconfig ??? parmove0 v) =
    mk_mconfig ??? parmove1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? (nth src ? v (niltape ?)) (Some ? 〈a1,D〉)) src)
       (tape_move ? (nth dst ? v (niltape ?)) (Some ? 〈a2,D〉)) dst).
#src #dst #sig #n #D #is_sep #v #Hneq #Hsrc #Hdst
#a1 #a2 #Hcursrc #Hcurdst #Hsep
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ whd in match (trans ????);
  >Hcursrc >Hcurdst whd in ⊢ (??(???%)?); >Hsep //
| whd in match (trans ????);
  >Hcursrc >Hcurdst whd in ⊢ (??(???????(???%))?); >Hsep
  change with (change_vec ?????) in ⊢ (??(???????%)?);
  <(change_vec_same … v dst (niltape ?)) in ⊢ (??%?);
  <(change_vec_same … v src (niltape ?)) in ⊢ (??%?);
  >pmap_change >pmap_change >tape_move_null_action
  @eq_f2 // @eq_f2 // >nth_change_vec_neq //
]
qed.

lemma sem_parmove_step :
  ∀src,dst,sig,n,D,is_sep.src ≠ dst → src < S n → dst < S n → 
  parmove_step src dst sig n D is_sep ⊨ 
    [ parmove1: R_parmove_step_true src dst sig n D is_sep, 
             R_parmove_step_false src dst sig n is_sep ].
#src #dst #sig #n #D #is_sep #Hneq #Hsrc #Hdst #int
lapply (refl ? (current ? (nth src ? int (niltape ?))))
cases (current ? (nth src ? int (niltape ?))) in ⊢ (???%→?);
[ #Hcursrc %{2} %
  [| % [ %
    [ whd in ⊢ (??%?); >parmove_q0_q2_null_src /2/
      <(nth_vec_map ?? (current …) src ? int (niltape ?)) //
    | normalize in ⊢ (%→?); #H destruct (H) ]
    | #_ % // % %2 // ] ]
| #a #Ha cases (true_or_false (is_sep a)) #Hsep
  [ %{2} %
    [| % [ %
      [ whd in ⊢ (??%?); >(parmove_q0_q2_sep … Hsep) /2/
        <(nth_vec_map ?? (current …) src ? int (niltape ?)) //
      | normalize in ⊢ (%→?); #H destruct (H) ]
      | #_ % // % % %{a} % // ] ]
  | lapply (refl ? (current ? (nth dst ? int (niltape ?))))
    cases (current ? (nth dst ? int (niltape ?))) in ⊢ (???%→?);
    [ #Hcurdst %{2} %
      [| % [ %
        [ whd in ⊢ (??%?); >(parmove_q0_q2_null_dst … Hsep) /2/ 
          [ <(nth_vec_map ?? (current …) dst ? int (niltape ?)) //
          | <(nth_vec_map ?? (current …) src ? int (niltape ?)) // ]
        | normalize in ⊢ (%→?); #H destruct (H) ]
        | #_ % // %2 // ] ]
    | #b #Hb %{2} %
      [| % [ % 
        [whd in ⊢  (??%?);  >(parmove_q0_q1 … Hneq Hsrc Hdst ? b ?? Hsep) //
          [ <(nth_vec_map ?? (current …) dst ? int (niltape ?)) //
          | <(nth_vec_map ?? (current …) src ? int (niltape ?)) // ]
        | #_ %{a} %{b} % // % // % // ]
        | * #H @False_ind @H % ]
]]]]
qed.

definition parmove ≝ λsrc,dst,sig,n,D,is_sep.
  whileTM … (parmove_step src dst sig n D is_sep) parmove1.

definition R_parmoveL ≝ 
  λsrc,dst,sig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  (∀ls,x,xs,rs,sep.
    nth src ? int (niltape ?) = midtape sig (xs@sep::ls) x rs →
    (∀c.memb ? c (x::xs) = true → is_sep c = false) → is_sep sep = true → 
    ∀ls0,x0,target,c,rs0.|xs| = |target| → 
    nth dst ? int (niltape ?) = midtape sig (target@c::ls0) x0 rs0 → 
    outt = change_vec ?? 
           (change_vec ?? int (midtape sig ls sep (reverse ? xs@x::rs)) src)
           (midtape sig ls0 c (reverse ? target@x0::rs0)) dst) ∧
  (((∃s.current ? (nth src ? int (niltape ?)) = Some ? s ∧ is_sep s = true) ∨  
     current ? (nth src ? int (niltape ?)) = None ? ∨
     current ? (nth dst ? int (niltape ?)) = None ?) →
     outt = int).
  
lemma wsem_parmoveL : ∀src,dst,sig,n,is_sep.src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L is_sep ⊫ R_parmoveL src dst sig n is_sep.
#src #dst #sig #n #is_sep #Hneq #Hsrc #Hdst #ta #k #outc #Hloop
lapply (sem_while … (sem_parmove_step src dst sig n L is_sep Hneq Hsrc Hdst) … Hloop) //
-Hloop * #tb * #Hstar @(star_ind_l ??????? Hstar) -Hstar
[ whd in ⊢ (%→?); * #H #Houtc % [2: #_ @Houtc ] cases H
  [ * [ * #x * #Hx #Hsep #ls #x0 #xs #rs #sep #Hsrctc #Hnosep >Hsrctc in Hx; normalize in ⊢ (%→?);
    #Hx0 destruct (Hx0) lapply (Hnosep ? (memb_hd …)) >Hsep
    #Hfalse destruct (Hfalse)
  | #Hcur_src #ls #x0 #xs #rs #sep #Hsrctc >Hsrctc in Hcur_src;
    normalize in ⊢ (%→?); #H destruct (H)]
  |#Hcur_dst  #ls #x0 #xs #rs #sep #Hsrctc #Hnosep #Hsep #ls0 #x1 #target 
   #c #rs0 #Hlen #Hdsttc >Hdsttc in Hcur_dst; normalize in ⊢ (%→?); #H destruct (H)
  ]  
| #td #te * #c0 * #c1 * * * #Hc0 #Hc1 #Hc0nosep #Hd #Hstar #IH #He 
  lapply (IH He) -IH * #IH1 #IH2 %
  [ #ls #x #xs #rs #sep #Hsrc_tc #Hnosep #Hsep #ls0 #x0 #target
    #c #rs0 #Hlen #Hdst_tc
   >Hsrc_tc in Hc0; normalize in ⊢ (%→?); #Hc0 destruct (Hc0)
   >Hdst_tc in Hd; >Hsrc_tc @(list_cases2 … Hlen)
    [ #Hxsnil #Htargetnil >Hxsnil >Htargetnil #Hd >IH2 
      [2: %1 %1 %{sep} % // >Hd >nth_change_vec_neq [|@(sym_not_eq … Hneq)]
      >nth_change_vec //]  
      >Hd -Hd @(eq_vec … (niltape ?))
      #i #Hi cases (decidable_eq_nat i src) #Hisrc
      [ >Hisrc >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
        >nth_change_vec //
        >(nth_change_vec_neq … src dst) [|@(sym_not_eq … Hneq)]
        >nth_change_vec //
      | cases (decidable_eq_nat i dst) #Hidst
        [ >Hidst >nth_change_vec // >nth_change_vec //
          >Hdst_tc in Hc1; >Htargetnil
          normalize in ⊢ (%→?); #Hc1 destruct (Hc1) %
        | >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)]
          >nth_change_vec_neq [|@(sym_not_eq … Hidst)]
          >nth_change_vec_neq [|@(sym_not_eq … Hisrc)] % 
        ]
      ]
    | #hd1 #hd2 #tl1 #tl2 #Hxs #Htarget >Hxs >Htarget #Hd
      >(IH1 ls hd1 tl1 (c0::rs) sep ?? Hsep ls0 hd2 tl2 c (x0::rs0))
      [ >Hd >(change_vec_commute … ?? td ?? src dst) //
       >change_vec_change_vec
       >(change_vec_commute … ?? td ?? dst src) [|@sym_not_eq //]
       >change_vec_change_vec
       >reverse_cons >associative_append
       >reverse_cons >associative_append % 
     | >Hd >nth_change_vec // >Hdst_tc >Htarget >Hdst_tc in Hc1;
       normalize in ⊢ (%→?); #H destruct (H) //
     | >Hxs in Hlen; >Htarget normalize #Hlen destruct (Hlen) //
     | <Hxs #c1 #Hc1 @Hnosep @memb_cons //
     | >Hd >nth_change_vec_neq [|@sym_not_eq //]
       >nth_change_vec // ]
   ]
 | >Hc0 >Hc1 * [* [ * #c * #Hc destruct (Hc) >Hc0nosep]] #Habs destruct (Habs)
 ] ]
qed.
 
lemma terminate_parmoveL :  ∀src,dst,sig,n,is_sep,t.
  src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L is_sep ↓ t.
#src #dst #sig #n #is_sep #t #Hneq #Hsrc #Hdst
@(terminate_while … (sem_parmove_step …)) //
<(change_vec_same … t src (niltape ?))
cases (nth src (tape sig) t (niltape ?))
[ % #t1 * #x1 * #x2 * * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct 
|2,3: #a0 #al0 % #t1 * #x1 * #x2 * * * >nth_change_vec // normalize in ⊢ (%→?); #Hx destruct
| #ls lapply t -t elim ls
  [#t #c #rs % #t1 * #x1 * #x2 * * * >nth_change_vec // normalize in ⊢ (%→?);
   #H1 destruct (H1) #Hcurdst #Hxsep >change_vec_change_vec #Ht1 % 
   #t2 * #y1 * #y2 * * * >Ht1 >nth_change_vec_neq [|@sym_not_eq //]
   >nth_change_vec // normalize in ⊢ (%→?); #H destruct (H)
  |#l0 #ls0 #IH #t #c #rs % #t1 * #x1 * #x2 * * * >nth_change_vec //
   normalize in ⊢ (%→?); #H destruct (H) #Hcurdst #Hxsep
   >change_vec_change_vec >change_vec_commute // #Ht1 >Ht1 @IH
  ]
]
qed.

lemma sem_parmoveL : ∀src,dst,sig,n,is_sep.
  src ≠ dst → src < S n → dst < S n → 
  parmove src dst sig n L is_sep ⊨ R_parmoveL src dst sig n is_sep.
#src #dst #sig #n #is_sep #Hneq #Hsrc #Hdst @WRealize_to_Realize 
[/2/ | @wsem_parmoveL //]
qed.