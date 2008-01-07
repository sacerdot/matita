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



include "excess.ma".

definition sequence := λO:excess.nat → O.

definition fun_of_sequence: ∀O:excess.sequence O → nat → O.
intros; apply s; assumption;
qed.

coercion cic:/matita/sequence/fun_of_sequence.con 1.

definition upper_bound ≝ 
  λO:excess.λa:sequence O.λu:O.∀n:nat.a n ≤ u.
  
definition lower_bound ≝ 
  λO:excess.λa:sequence O.λu:O.∀n:nat.u ≤ a n.

definition strong_sup ≝
  λO:excess.λs:sequence O.λx.
    upper_bound ? s x ∧ (∀y:O.x ≰ y → ∃n.s n ≰ y).
  
definition strong_inf ≝
  λO:excess.λs:sequence O.λx.
    lower_bound ? s x ∧ (∀y:O.y ≰ x → ∃n.y ≰ s n).

definition weak_sup ≝
  λO:excess.λs:sequence O.λx.
    upper_bound ? s x ∧ (∀y:O.upper_bound ? s y → x ≤ y).
  
definition weak_inf ≝
  λO:excess.λs:sequence O.λx.
    lower_bound ? s x ∧ (∀y:O.lower_bound ? s y → y ≤ x).

lemma strong_sup_is_weak: 
  ∀O:excess.∀s:sequence O.∀x:O.strong_sup ? s x → weak_sup ? s x.
intros (O s x Ssup); elim Ssup (Ubx M); clear Ssup; split; [assumption]
intros 3 (y Uby E); cases (M ? E) (n En); unfold in Uby; cases (Uby ? En);
qed.
 
lemma strong_inf_is_weak: 
  ∀O:excess.∀s:sequence O.∀x:O.strong_inf ? s x → weak_inf ? s x.
intros (O s x Ssup); elim Ssup (Ubx M); clear Ssup; split; [assumption]
intros 3 (y Uby E); cases (M ? E) (n En); unfold in Uby; cases (Uby ? En);
qed.

include "ordered_group.ma".
include "nat/orders.ma".

definition tends0 ≝ 
  λO:pogroup.λs:sequence O.
    ∀e:O.0 < e → ∃N.∀n.N < n → -e < s n ∧ s n < e.
    
definition increasing ≝ 
  λO:excess.λa:sequence O.∀n:nat.a n ≤ a (S n).

definition decreasing ≝ 
  λO:excess.λa:sequence O.∀n:nat.a (S n) ≤ a n.




(*

definition is_upper_bound ≝ λO:excess.λa:sequence O.λu:O.∀n:nat.a n ≤ u.
definition is_lower_bound ≝ λO:excess.λa:sequence O.λu:O.∀n:nat.u ≤ a n.

record is_sup (O:excess) (a:sequence O) (u:O) : Prop ≝
 { sup_upper_bound: is_upper_bound O a u; 
   sup_least_upper_bound: ∀v:O. is_upper_bound O a v → u≤v
 }.

record is_inf (O:excess) (a:sequence O) (u:O) : Prop ≝
 { inf_lower_bound: is_lower_bound O a u; 
   inf_greatest_lower_bound: ∀v:O. is_lower_bound O a v → v≤u
 }.

record is_bounded_below (O:excess) (a:sequence O) : Type ≝
 { ib_lower_bound: O;
   ib_lower_bound_is_lower_bound: is_lower_bound ? a ib_lower_bound
 }.

record is_bounded_above (O:excess) (a:sequence O) : Type ≝
 { ib_upper_bound: O;
   ib_upper_bound_is_upper_bound: is_upper_bound ? a ib_upper_bound
 }.

record is_bounded (O:excess) (a:sequence O) : Type ≝
 { ib_bounded_below:> is_bounded_below ? a;
   ib_bounded_above:> is_bounded_above ? a
 }.

record bounded_below_sequence (O:excess) : Type ≝
 { bbs_seq:> sequence O;
   bbs_is_bounded_below:> is_bounded_below ? bbs_seq
 }.

record bounded_above_sequence (O:excess) : Type ≝
 { bas_seq:> sequence O;
   bas_is_bounded_above:> is_bounded_above ? bas_seq
 }.

record bounded_sequence (O:excess) : Type ≝
 { bs_seq:> sequence O;
   bs_is_bounded_below: is_bounded_below ? bs_seq;
   bs_is_bounded_above: is_bounded_above ? bs_seq
 }.

definition bounded_below_sequence_of_bounded_sequence ≝
 λO:excess.λb:bounded_sequence O.
  mk_bounded_below_sequence ? b (bs_is_bounded_below ? b).

coercion cic:/matita/sequence/bounded_below_sequence_of_bounded_sequence.con.

definition bounded_above_sequence_of_bounded_sequence ≝
 λO:excess.λb:bounded_sequence O.
  mk_bounded_above_sequence ? b (bs_is_bounded_above ? b).

coercion cic:/matita/sequence/bounded_above_sequence_of_bounded_sequence.con.

definition lower_bound ≝
 λO:excess.λb:bounded_below_sequence O.
  ib_lower_bound ? b (bbs_is_bounded_below ? b).

lemma lower_bound_is_lower_bound:
 ∀O:excess.∀b:bounded_below_sequence O.
  is_lower_bound ? b (lower_bound ? b).
intros; unfold lower_bound; apply ib_lower_bound_is_lower_bound.
qed.

definition upper_bound ≝
 λO:excess.λb:bounded_above_sequence O.
  ib_upper_bound ? b (bas_is_bounded_above ? b).

lemma upper_bound_is_upper_bound:
 ∀O:excess.∀b:bounded_above_sequence O.
  is_upper_bound ? b (upper_bound ? b).
intros; unfold upper_bound; apply ib_upper_bound_is_upper_bound.
qed.

definition reverse_excess: excess → excess.
intros (E); apply (mk_excess E); [apply (λx,y.exc_relation E y x)] 
cases E (T f cRf cTf); simplify; 
[1: unfold Not; intros (x H); apply (cRf x); assumption
|2: intros (x y z); apply Or_symmetric; apply cTf; assumption;]
qed. 

definition reverse_excess: excess → excess.
intros (p); apply (mk_excess (reverse_excess p));
generalize in match (reverse_excess p); intros (E);
apply mk_is_porder_relation;
[apply le_reflexive|apply le_transitive|apply le_antisymmetric]
qed. 
 
lemma is_lower_bound_reverse_is_upper_bound:
 ∀O:excess.∀a:sequence O.∀l:O.
  is_lower_bound O a l → is_upper_bound (reverse_excess O) a l.
intros (O a l H); unfold; intros (n); unfold reverse_excess;
unfold reverse_excess; simplify; fold unfold le (le ? l (a n)); apply H;    
qed.

lemma is_upper_bound_reverse_is_lower_bound:
 ∀O:excess.∀a:sequence O.∀l:O.
  is_upper_bound O a l → is_lower_bound (reverse_excess O) a l.
intros (O a l H); unfold; intros (n); unfold reverse_excess;
unfold reverse_excess; simplify; fold unfold le (le ? (a n) l); apply H;    
qed.

lemma reverse_is_lower_bound_is_upper_bound:
 ∀O:excess.∀a:sequence O.∀l:O.
  is_lower_bound (reverse_excess O) a l → is_upper_bound O a l.
intros (O a l H); unfold; intros (n); unfold reverse_excess in H;
unfold reverse_excess in H; simplify in H; apply H;    
qed.

lemma reverse_is_upper_bound_is_lower_bound:
 ∀O:excess.∀a:sequence O.∀l:O.
  is_upper_bound (reverse_excess O) a l → is_lower_bound O a l.
intros (O a l H); unfold; intros (n); unfold reverse_excess in H;
unfold reverse_excess in H; simplify in H; apply H;    
qed.

lemma is_inf_to_reverse_is_sup:
 ∀O:excess.∀a:bounded_below_sequence O.∀l:O.
  is_inf O a l → is_sup (reverse_excess O) a l.
intros (O a l H); apply (mk_is_sup (reverse_excess O));
[1: apply is_lower_bound_reverse_is_upper_bound; apply inf_lower_bound; assumption
|2: unfold reverse_excess; simplify; unfold reverse_excess; simplify; 
    intros (m H1); apply (inf_greatest_lower_bound ? ? ? H); apply H1;]
qed.

lemma is_sup_to_reverse_is_inf:
 ∀O:excess.∀a:bounded_above_sequence O.∀l:O.
  is_sup O a l → is_inf (reverse_excess O) a l.
intros (O a l H); apply (mk_is_inf (reverse_excess O));
[1: apply is_upper_bound_reverse_is_lower_bound; apply sup_upper_bound; assumption
|2: unfold reverse_excess; simplify; unfold reverse_excess; simplify; 
    intros (m H1); apply (sup_least_upper_bound ? ? ? H); apply H1;]
qed.

lemma reverse_is_sup_to_is_inf:
 ∀O:excess.∀a:bounded_above_sequence O.∀l:O.
  is_sup (reverse_excess O) a l → is_inf O a l.
intros (O a l H); apply mk_is_inf;
[1: apply reverse_is_upper_bound_is_lower_bound; 
    apply (sup_upper_bound (reverse_excess O)); assumption
|2: intros (v H1); apply (sup_least_upper_bound (reverse_excess O) a l H v);
    apply is_lower_bound_reverse_is_upper_bound; assumption;]
qed.

lemma reverse_is_inf_to_is_sup:
 ∀O:excess.∀a:bounded_above_sequence O.∀l:O.
  is_inf (reverse_excess O) a l → is_sup O a l.
intros (O a l H); apply mk_is_sup;
[1: apply reverse_is_lower_bound_is_upper_bound; 
    apply (inf_lower_bound (reverse_excess O)); assumption
|2: intros (v H1); apply (inf_greatest_lower_bound (reverse_excess O) a l H v);
    apply is_upper_bound_reverse_is_lower_bound; assumption;]
qed.

*)