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

include "nat/minus.ma".
include "list/list.ma".

interpretation "list nth" 'nth = (nth ?).
interpretation "list nth" 'nth_appl l d i = (nth ? l d i).
notation "\nth" with precedence 90 for @{'nth}.
notation < "\nth \nbsp term 90 l \nbsp term 90 d \nbsp term 90 i" 
with precedence 69 for @{'nth_appl $l $d $i}.

definition make_list ≝
  λA:Type.λdef:nat→A.
    let rec make_list (n:nat) on n ≝
      match n with [ O ⇒ nil ? | S m ⇒ def m :: make_list m]
    in make_list.

interpretation "\mk_list appl" 'mk_list_appl f n = (make_list ? f n).
interpretation "\mk_list" 'mk_list = (make_list ?).   
notation "\mk_list" with precedence 90 for @{'mk_list}.
notation < "\mk_list \nbsp term 90 f \nbsp term 90 n" 
with precedence 69 for @{'mk_list_appl $f $n}.

notation "\len" with precedence 90 for @{'len}.
interpretation "len" 'len = (length ?).
notation < "\len \nbsp term 90 l" with precedence 69 for @{'len_appl $l}.
interpretation "len appl" 'len_appl l = (length ? l).

lemma mk_list_ext: ∀T:Type.∀f1,f2:nat→T.∀n. (∀x.x<n → f1 x = f2 x) → \mk_list f1 n = \mk_list f2 n.
intros 4;elim n; [reflexivity] simplify; rewrite > H1; [2: apply le_n]
apply eq_f; apply H; intros; apply H1; apply (trans_le ??? H2); apply le_S; apply le_n;
qed.

lemma len_mk_list : ∀T:Type.∀f:nat→T.∀n.\len (\mk_list f n) = n.
intros; elim n; [reflexivity] simplify; rewrite > H; reflexivity;
qed.

record rel (rel_T : Type) : Type ≝ {
  rel_op :2> rel_T → rel_T → Prop
}.

record trans_rel : Type ≝ {
  o_T :> Type;
  o_rel :> rel o_T;
  o_tra : ∀x,y,z: o_T.o_rel x y → o_rel y z → o_rel x z 
}.

lemma trans: ∀r:trans_rel.∀x,y,z:r.r x y → r y z → r x z.
apply o_tra;
qed.

inductive sorted (lt : trans_rel): list (o_T lt) → Prop ≝ 
| sorted_nil : sorted lt []
| sorted_one : ∀x. sorted lt [x]
| sorted_cons : ∀x,y,tl. lt x y → sorted lt (y::tl) → sorted lt (x::y::tl). 

lemma nth_nil: ∀T,i.∀def:T. \nth [] def i = def.
intros; elim i; simplify; [reflexivity;] assumption; qed.

lemma len_append: ∀T:Type.∀l1,l2:list T. \len (l1@l2) = \len l1 + \len l2.
intros; elim l1; [reflexivity] simplify; rewrite < H; reflexivity;
qed.

coinductive non_empty_list (A:Type) : list A → Type := 
| show_head: ∀x,l. non_empty_list A (x::l).

lemma len_gt_non_empty : 
  ∀T.∀l:list T.O < \len l → non_empty_list T l.
intros; cases l in H; [intros; cases (not_le_Sn_O ? H);] intros; constructor 1;
qed. 

lemma sorted_tail: ∀r,x,l.sorted r (x::l) → sorted r l.
intros; inversion H; intros; [destruct H1;|destruct H1;constructor 1;]
destruct H4; assumption;
qed.

lemma sorted_skip: ∀r,x,y,l. sorted r (x::y::l) → sorted r (x::l).
intros (r x y l H1); inversion H1; intros; [1,2: destruct H]
destruct H4; inversion H2; intros; [destruct H4]
[1: destruct H4; constructor 2;
|2: destruct H7; constructor 3; 
    [ apply (o_tra ? ??? H H4); | apply (sorted_tail ??? H2);]]
qed.

lemma sorted_tail_bigger : ∀r,x,l,d.sorted r (x::l) → ∀i. i < \len l → r x (\nth l d i).
intros 4; elim l; [ cases (not_le_Sn_O i H1);]
cases i in H2;
[2: intros; apply (H ? n);[apply (sorted_skip ???? H1)|apply le_S_S_to_le; apply H2]
|1: intros; inversion H1; intros; [1,2: destruct H3]
    destruct H6; simplify; assumption;]
qed. 

(* move in nat/ *)
lemma lt_n_plus_n_Sm : ∀n,m:nat.n < n + S m.
intros; rewrite > sym_plus; apply (le_S_S n (m+n)); alias id "le_plus_n" = "cic:/matita/nat/le_arith/le_plus_n.con".
apply (le_plus_n m n); qed.

lemma nth_append_lt_len:
  ∀T:Type.∀l1,l2:list T.∀def.∀i.i < \len l1 → \nth (l1@l2) def i = \nth l1 def i.
intros 4; elim l1; [cases (not_le_Sn_O ? H)] cases i in H H1; simplify; intros;
[reflexivity| rewrite < H;[reflexivity] apply le_S_S_to_le; apply H1]
qed. 

lemma nth_append_ge_len:
  ∀T:Type.∀l1,l2:list T.∀def.∀i.
    \len l1 ≤ i → \nth (l1@l2) def i = \nth l2 def (i - \len l1).
intros 4; elim l1; [ rewrite < minus_n_O; reflexivity]
cases i in H1; simplify; intros; [cases (not_le_Sn_O ? H1)]
apply H; apply le_S_S_to_le; apply H1;
qed. 

lemma nth_len:
  ∀T:Type.∀l1,l2:list T.∀def,x.
    \nth (l1@x::l2) def (\len l1) = x.
intros 2; elim l1;[reflexivity] simplify; apply H; qed.

lemma sorted_head_smaller:
  ∀r,l,p,d. sorted r (p::l) → ∀i.i < \len l → r p (\nth l d i).
intros 2 (r l); elim l; [cases (not_le_Sn_O ? H1)] cases i in H2; simplify; intros;
[1: inversion H1; [1,2: simplify; intros; destruct H3] intros; destruct H6; assumption; 
|2: apply (H p ?? n ?); [apply (sorted_skip ???? H1)] apply le_S_S_to_le; apply H2]
qed.

alias symbol "lt" = "natural 'less than'".
lemma sorted_pivot:
  ∀r,l1,l2,p,d. sorted r (l1@p::l2) → 
    (∀i. i < \len l1 → r (\nth l1 d i) p) ∧
    (∀i. i < \len l2 → r p (\nth l2 d i)).
intros 2 (r l); elim l; 
[1: split; [intros; cases (not_le_Sn_O ? H1);] intros;
    apply sorted_head_smaller; assumption;
|2: simplify in H1; cases (H ?? d (sorted_tail ??? H1));
    lapply depth = 0 (sorted_head_smaller ??? d H1) as Hs;
    split; simplify; intros;
    [1: cases i in H4; simplify; intros; 
        [1: lapply depth = 0 (Hs (\len l1)) as HS; 
            rewrite > nth_len in HS; apply HS;
            rewrite > len_append; simplify; apply lt_n_plus_n_Sm;
        |2: apply (H2 n); apply le_S_S_to_le; apply H4]
    |2: apply H3; assumption]]
qed.

coinductive cases_bool (p:bool) : bool → CProp ≝
| case_true : p = true → cases_bool p true
| cases_false : p = false → cases_bool p false.

lemma case_b : ∀A:Type.∀f:A → bool. ∀x.cases_bool (f x) (f x).
intros; cases (f x);[left;|right] reflexivity;
qed. 

coinductive break_spec (T : Type) (n : nat) (l : list T) : list T → CProp ≝
| break_to: ∀l1,x,l2. \len l1 = n → l = l1 @ [x] @ l2 → break_spec T n l l.     

lemma list_break: ∀T,n,l. n < \len l → break_spec T n l l.
intros 2; elim n;
[1: elim l in H; [cases (not_le_Sn_O ? H)]
    apply (break_to ?? ? [] a l1); reflexivity;
|2: cases (H l); [2: apply lt_S_to_lt; assumption;] cases l2 in H3; intros;
    [1: rewrite < H2 in H1; rewrite > H3 in H1; rewrite > append_nil in H1;
        rewrite > len_append in H1; rewrite > plus_n_SO in H1;
        cases (not_le_Sn_n ? H1);
    |2: apply (break_to ?? ? (l1@[x]) t l3); 
        [2: simplify; rewrite > associative_append; assumption;
        |1: rewrite < H2; rewrite > len_append; rewrite > plus_n_SO; reflexivity]]]
qed.

include "logic/cprop_connectives.ma".

definition eject_N ≝
  λP.λp:∃x:nat.P x.match p with [ex_introT p _ ⇒ p].
coercion eject_N.
definition inject_N ≝ λP.λp:nat.λh:P p. ex_introT ? P p h.
coercion inject_N with 0 1 nocomposites.

coinductive find_spec (T:Type) (P:T→bool) (l:list T) (d:T) (res : nat) : nat → CProp ≝
| found: 
    ∀i. i < \len l → P (\nth l d i) = true → res = i →  
    (∀j. j < i → P (\nth l d j) = false) → find_spec T P l d res i  
| not_found: ∀i. i = \len l → res = i →
    (∀j.j < \len l → P (\nth l d j) = false) → find_spec T P l d res i.

lemma find_lemma : ∀T.∀P:T→bool.∀l:list T.∀d.∃i.find_spec ? P l d i i.
intros;
letin find ≝ (
  let rec aux (acc: nat) (l : list T) on l : nat ≝
    match l with
    [ nil ⇒ acc
    | cons x tl ⇒
        match P x with
        [ false ⇒ aux (S acc) tl   
        | true ⇒ acc]]
  in aux :
  ∀acc,l1.∃p:nat.
    ∀story. story @ l1 = l → acc = \len story →
    find_spec ? P story d acc acc → 
    find_spec ? P (story @ l1) d p p);
[4: clearbody find; cases (find 0 l);
    lapply (H [] (refl_eq ??) (refl_eq ??)) as K;
    [2: apply (not_found ?? [] d); intros; try reflexivity; cases (not_le_Sn_O ? H1);
    |1: cases K; clear K;
        [2: exists[apply (\len l)]
            apply not_found; try reflexivity; apply H3;
        |1: exists[apply i] apply found;  try reflexivity; assumption;]]
|1: intros; cases (aux (S n) l2); simplify; clear aux;
    lapply depth = 0 (H5 (story@[t])) as K; clear H5;
    change with (find_spec ? P (story @ ([t] @ l2)) d w w);
    rewrite < associative_append; apply K; clear K;
    [1: rewrite > associative_append; apply H2;
    |2: rewrite > H3; rewrite > len_append; rewrite > sym_plus; reflexivity;
    |3: cases H4; clear H4; destruct H7;
        [2: rewrite > H5; rewrite > (?:S (\len story) = \len (story @ [t])); [2:
              rewrite > len_append; rewrite > sym_plus; reflexivity;]
            apply not_found; try reflexivity; intros; cases (cmp_nat (S j) (\len story));
            [1: rewrite > (nth_append_lt_len ????? H8); apply H7; apply H8;
            |2: rewrite > (nth_append_ge_len ????? (le_S_S_to_le ?? H8));
                rewrite > (?: j - \len story = 0);[assumption]
                rewrite > (?:j = \len story);[rewrite > minus_n_n; reflexivity]
                apply le_to_le_to_eq; [2: apply le_S_S_to_le; assumption;] 
                rewrite > len_append in H4;rewrite > sym_plus in H4; 
                apply le_S_S_to_le; apply H4;]
        |1: rewrite < H3 in H5; cases (not_le_Sn_n ? H5);]]
|2: intros; cases H4; clear H4; 
    [1: destruct H7; rewrite > H3 in H5; cases (not_le_Sn_n ? H5); 
    |2: apply found; try reflexivity;
        [1: rewrite > len_append; simplify; rewrite > H5; apply lt_n_plus_n_Sm;
        |2: rewrite > H5; rewrite > nth_append_ge_len; [2: apply le_n]
            rewrite < minus_n_n; assumption;
        |3: intros; rewrite > H5 in H4; rewrite > nth_append_lt_len; [2:assumption]
            apply H7; assumption]]
|3: intros; rewrite > append_nil; assumption;]
qed.

lemma find : ∀T:Type.∀P:T→bool.∀l:list T.∀d:T.nat.
intros; cases (find_lemma ? f l t); apply w; qed.

lemma cases_find: ∀T,P,l,d. find_spec T P l d (find T P l d) (find T P l d).
intros; unfold find; cases (find_lemma T P l d); simplify; assumption; qed.

lemma list_elim_with_len:
  ∀T:Type.∀P: nat → list T → CProp.
    P O [] → (∀l,a,n.P (\len l) l → P (S n) (a::l)) →
     ∀l.P (\len l) l.
intros;elim l; [assumption] simplify; apply H1; apply H2;
qed.
 
lemma sorted_near:
 ∀r,l. sorted r l → ∀i,d. S i < \len l → r (\nth l d i) (\nth l d (S i)).
 intros 3; elim H; 
 [1: cases (not_le_Sn_O ? H1);
 |2: simplify in H1; cases (not_le_Sn_O ? (le_S_S_to_le ?? H1));
 |3: simplify; cases i in H4; intros; [apply H1]
     apply H3; apply le_S_S_to_le; apply H4]
qed.  
 
definition last ≝
 λT:Type.λd.λl:list T. \nth l d (pred (\len l)).

notation > "\last" non associative with precedence 90 for @{'last}.
notation < "\last d l" non associative with precedence 70 for @{'last2 $d $l}.
interpretation "list last" 'last = (last ?). 
interpretation "list last applied" 'last2 d l = (last ? d l).

definition head ≝
 λT:Type.λd.λl:list T.\nth l d O.

notation > "\hd" non associative with precedence 90 for @{'hd}.
notation < "\hd d l" non associative with precedence 70 for @{'hd2 $d $l}.
interpretation "list head" 'hd = (head ?).
interpretation "list head applied" 'hd2 d l = (head ? d l).

