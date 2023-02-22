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

include "models/q_bars.ma".

(* move in nat/minus *)
lemma minus_lt : ∀i,j. i < j → j - i = S (j - S i). 
intros 2;
apply (nat_elim2 ???? i j); simplify; intros;
[1: cases n in H; intros; rewrite < minus_n_O; [cases (not_le_Sn_O ? H);]
    simplify; rewrite < minus_n_O; reflexivity;
|2: cases (not_le_Sn_O ? H);
|3: apply H; apply le_S_S_to_le; assumption;]
qed.

alias symbol "lt" = "bar lt".
lemma inversion_sorted:
  ∀a,l. sorted q2_lt (a::l) → Or (a < \hd ▭ l) (l = []).
intros 2; elim l; [right;reflexivity] left; inversion H1; intros;
[1,2:destruct H2| destruct H5; assumption]
qed.

lemma inversion_sorted2:
  ∀a,b,l. sorted q2_lt (a::b::l) → a < b.
intros; inversion H; intros; [1,2:destruct H1] destruct H4; assumption; 
qed.

let rec copy (l : list bar) on l : list bar ≝
  match l with
  [ nil ⇒ []
  | cons x tl ⇒ 〈\fst x, 〈OQ,OQ〉〉 :: copy tl].

lemma sorted_copy:
  ∀l:list bar.sorted q2_lt l → sorted q2_lt (copy l).
intro l; elim l; [apply (sorted_nil q2_lt)] simplify;
cases l1 in H H1; simplify; intros; [apply (sorted_one q2_lt)]
apply (sorted_cons q2_lt); [2: apply H; apply (sorted_tail q2_lt ?? H1);]
apply (inversion_sorted2 ??? H1);
qed.

lemma len_copy: ∀l. \len (copy l) = \len l. 
intro; elim l; [reflexivity] simplify; apply eq_f; assumption;
qed.

lemma copy_same_bases: ∀l. same_bases l (copy l).
intros; elim l; [intro; reflexivity] intro; simplify; cases i; [reflexivity]
simplify; apply (H n);
qed.

lemma copy_OQ : ∀l,n.nth_height (copy l) n = 〈OQ,OQ〉.
intro; elim l; [elim n;[reflexivity] simplify; assumption]
simplify; cases n; [reflexivity] simplify; apply (H n1);
qed.

lemma prepend_sorted_with_same_head:
 ∀r,x,l1,l2,d1,d2.
   sorted r (x::l1) → sorted r l2 → 
   (r x (\nth l1 d1 O) → r x (\nth l2 d2 O)) → (l1 = [] → r x d1) →
   sorted r (x::l2).
intros 8 (R x l1 l2 d1 d2 Sl1 Sl2);  inversion Sl1; inversion Sl2;
intros; destruct; try assumption; [3: apply (sorted_one R);]
[1: apply sorted_cons;[2:assumption] apply H2; apply H3; reflexivity;
|2: apply sorted_cons;[2: assumption] apply H5; apply H6; reflexivity;
|3: apply sorted_cons;[2: assumption] apply H5; assumption;
|4: apply sorted_cons;[2: assumption] apply H8; apply H4;]
qed.

lemma move_head_sorted: ∀x,l1,l2. 
  sorted q2_lt (x::l1) → sorted q2_lt l2 → nth_base l2 O = nth_base l1 O →
    l1 ≠ [] → sorted q2_lt (x::l2).
intros; apply (prepend_sorted_with_same_head q2_lt x l1 l2 ▭ ▭);
try assumption; intros; unfold nth_base in H2; whd in H4;
[1: rewrite < H2 in H4; assumption;
|2: cases (H3 H4);]
qed.
       

lemma sort_q2lt_same_base:
  ∀b,h1,h2,l. sorted q2_lt (〈b,h1〉::l) → sorted q2_lt (〈b,h2〉::l).
intros; cases (inversion_sorted ?? H); [2: rewrite > H1; apply (sorted_one q2_lt)]
lapply (sorted_tail q2_lt ?? H) as K; clear H; cases l in H1 K; simplify; intros;
[apply (sorted_one q2_lt);|apply (sorted_cons q2_lt);[2: assumption] apply H]
qed.

lemma value_head : ∀a,l,i.Qpos i ≤ \fst a → value_simple (a::l) i = \snd a.
intros; unfold value_simple; unfold match_domain; cases (cases_find bar (match_pred i) (a::l) ▭);
[1: cases i1 in H2 H3 H4; intros; [reflexivity] lapply (H4 O) as K; [2: apply le_S_S; apply le_O_n;]
    simplify in K; unfold match_pred in K; cases (q_cmp (Qpos i) (\fst a)) in K;
    simplify; intros; [destruct H6] lapply (q_le_lt_trans ??? H H5) as K; cases (q_lt_corefl ? K); 
|2: cases (?:False); lapply (H3 0); [2: simplify; apply le_S_S; apply le_O_n;]
    unfold match_pred in Hletin; simplify in Hletin; cases (q_cmp (Qpos i) (\fst a)) in Hletin;
    simplify; intros; [destruct H5] lapply (q_le_lt_trans ??? H H4); apply (q_lt_corefl ? Hletin);]
qed.

lemma value_unit : ∀x,i. value_simple [x] i = \snd x.
intros; unfold value_simple; unfold match_domain;
cases (cases_find bar (match_pred i) [x] ▭);
[1: cases i1 in H; intros; [reflexivity] simplify in H;
    cases (not_le_Sn_O ? (le_S_S_to_le ?? H));
|2: simplify in H; destruct H; reflexivity;]
qed.

lemma value_tail : 
  ∀a,b,l,i.\fst a < Qpos i → \fst b ≤ Qpos i → value_simple (a::b::l) i = value_simple (b::l) i.
intros; unfold value_simple; unfold match_domain;
cases (cases_find bar (match_pred i) (a::b::l) ▭);
[1: cases i1 in H3 H2 H4 H5; intros 1; simplify in ⊢ (? ? (? ? %) ?→?); unfold in ⊢ (? ? % ?→?); intros;
    [1: cases (?:False); cases (q_cmp (Qpos i) (\fst a)) in H3; simplify; intros;[2: destruct H6]
        apply (q_lt_corefl ? (q_lt_le_trans ??? H H3));
    |2:         

normalize in ⊢ (? ? % ?→?); simplify;
[1: rewrite > (value_head);
 
lemma value_copy : 
  ∀l,i.rewrite > (value_u
  value_simple (copy l) i = 〈OQ,OQ〉.
intros; elim l;
[1: reflexivity;
|2: cases l1 in H; intros; simplify in ⊢ (? ? (? % ?) ?);
    [1: rewrite > (value_unit); reflexivity;
    |2: cases (q_cmp (\fst b) (Qpos i));  
 
 change with (\fst ▭ = \lamsimplify in ⊢ (? ? (? % ?) ?); unfold value_simple; unfold match_domain; 
    cases (cases_find bar (match_pred i) [〈\fst x,〈OQ,OQ〉〉] ▭);
    [1: simplify in H1:(??%%);

 unfold match_pred;
    rewrite > (value_unit 〈\fst a,〈OQ,OQ〉〉); reflexivity;
|2: intros; simplify in H2 H3 H4 ⊢ (? ? (? % ? ? ? ?) ?);
    cases (q_cmp (Qpos i)  (\fst b));
    [2: rewrite > (value_tail ??? H2 H3 ? H4 H1); apply H;
    |1: rewrite > (value_head ??? H2 H3 ? H4 H1); reflexivity]]
qed. 
    