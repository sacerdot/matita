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

definition R_copy_step ≝ 
  λsrc,dst,sig,n,is_sep.λint,outt: Vector (tape sig) (S n).
  (∀x1,x2,xls,xrs.
   nth src ? int (niltape ?) = midtape sig xls x1 (x2::xrs) →
   (is_sep x1 = true ∧ outt = int) ∨
   (is_sep x1 = false ∧
    outt = change_vec ?? 
            (change_vec ?? int (midtape sig (x1::xls) x2 xrs) src)
            (tape_move ? (nth dst ? int (niltape ?)) (Some ? 〈x1,R〉)) dst)) ∧
  (current ? (nth src ? int (niltape ?)) = None ? → 
   outt = int).

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
  ∀src,dst,sig,n,is_sep,v,t.src < S n → dst < S n → 
  ∀s.current ? t = Some ? s → is_sep s = false → 
  step sig n (copy_step src dst sig n is_sep)
    (mk_mconfig ??? copy0 (change_vec ? (S n) v t src)) =
    mk_mconfig ??? copy1 
     (change_vec ? (S n) 
       (change_vec ?? v
         (tape_move ? (nth src ? v (niltape ?)) (Some ? 〈s,R〉)) src)
       (tape_move ? (nth dst ? v (niltape ?)) (Some ? 〈s,R〉)) dst).
#src #dst #sig #n #is_sep #v #t #Hsrc #Hdst #s #Hcurrent #Hsep
whd in ⊢ (??%?); >(eq_pair_fst_snd … (trans ????)) whd in ⊢ (??%?); @eq_f2
[ >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???%)?); >Hsep %
| >current_chars_change_vec // whd in match (trans ????);
  >nth_change_vec // >Hcurrent whd in ⊢ (??(???????(???%))?);
  >Hsep whd in ⊢ (??(???????(???%))?); >pmap_change
  (* le due change commutano *)
]

lemma sem_copy_step :
  ∀src,dst,sig,n,is_sep.src < S n → dst < S n → 
  copy_step src dst sig n is_sep ⊨ R_copy_step src dst sig n is_sep.
#src #dst #sig #n #is_sep #Hsrc #Hdst #int
<(change_vec_same ?? int src (niltape ?)) cases (nth src ? int (niltape ?))
[ %{2} % [| % 
  [ whd in ⊢ (??%?); >copy_q0_q2 // 
  | % // #x1 #x2 #xls #xrs >nth_change_vec // #Hfalse destruct ] ]
| #a #al %{2} % [| % 
  [ whd in ⊢ (??%?); >copy_q0_q2 // 
  | % // #x1 #x2 #xls #xrs >nth_change_vec // #Hfalse destruct ] ]
| #a #al %{2} % [| % 
  [ whd in ⊢ (??%?); >copy_q0_q2 // 
  | % // #x1 #x2 #xls #xrs >nth_change_vec // #Hfalse destruct ] ]
| #ls #c #rs %{2} % [| %
  [  