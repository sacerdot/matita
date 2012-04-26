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

include "dama/nat_ordered_set.ma".
include "models/q_support.ma".
include "models/list_support.ma". 
include "logic/cprop_connectives.ma". 

definition bar ≝ ℚ × (ℚ × ℚ).

notation < "\rationals \sup 2" non associative with precedence 90 for @{'q2}.
interpretation "Q x Q" 'q2 = (Prod Q Q).

definition empty_bar : bar ≝ 〈Qpos one,〈OQ,OQ〉〉.
notation "\rect" with precedence 90 for @{'empty_bar}.
interpretation "q0" 'empty_bar = empty_bar.

notation < "\ldots\rect\square\EmptySmallSquare\ldots" with precedence 90 for @{'lq2}.
interpretation "lq2" 'lq2 = (list bar). 

definition q2_lt := mk_rel bar (λx,y:bar.\fst x < \fst y).

interpretation "bar lt" 'lt x y = (rel_op ? q2_lt x y).

lemma q2_trans : ∀a,b,c:bar. a < b → b < c → a < c.
intros 3; cases a; cases b; cases c; unfold q2_lt; simplify; intros;
apply (q_lt_trans ??? H H1);
qed. 

definition q2_trel := mk_trans_rel bar q2_lt q2_trans.

interpretation "bar lt" 'lt x y = (FunClass_2_OF_trans_rel q2_trel x y).

definition canonical_q_lt : rel bar → trans_rel ≝ λx:rel bar.q2_trel.

coercion canonical_q_lt with nocomposites.

interpretation "bar lt" 'lt x y = (FunClass_2_OF_trans_rel (canonical_q_lt ?) x y).

definition nth_base ≝ λf,n. \fst (\nth f ▭ n).
definition nth_height ≝ λf,n. \snd (\nth f ▭ n).

record q_f : Type ≝ {
 bars: list bar; 
 bars_sorted : sorted q2_lt bars;
 bars_begin_OQ : nth_base bars O = OQ;
 bars_end_OQ : nth_height bars (pred (\len bars)) = 〈OQ,OQ〉
}.

lemma len_bases_gt_O: ∀f.O < \len (bars f).
intros; generalize in match (bars_begin_OQ f); cases (bars f); intros;
[2: simplify; apply le_S_S; apply le_O_n;
|1: normalize in H; destruct H;]
qed. 

lemma all_bases_positive : ∀f:q_f.∀i. OQ < nth_base (bars f) (S i).
intro f; generalize in match (bars_begin_OQ f); generalize in match (bars_sorted f);
cases (len_gt_non_empty ?? (len_bases_gt_O f)); intros;
cases (cmp_nat (\len l) i);
[2: lapply (sorted_tail_bigger q2_lt ?? ▭ H ? H2) as K;  
    simplify in H1; rewrite < H1; apply K;
|1: simplify; elim l in i H2;[simplify; rewrite > nth_nil; apply (q_pos_OQ one)]
    cases n in H3; intros; [simplify in H3; cases (not_le_Sn_O ? H3)] 
    apply (H2 n1); simplify in H3; apply (le_S_S_to_le ?? H3);]
qed.

alias symbol "lt" (instance 9) = "Q less than".
alias symbol "lt" (instance 7) = "natural 'less than'".
alias symbol "lt" (instance 6) = "natural 'less than'".
alias symbol "lt" (instance 5) = "Q less than".
alias symbol "lt" (instance 4) = "natural 'less than'".
alias symbol "lt" (instance 2) = "natural 'less than'".
alias symbol "leq" = "Q less or equal than".
coinductive value_spec (f : list bar) (i : ℚ) : ℚ × ℚ → CProp ≝
| value_of : ∀j,q. 
    nth_height f j = q →  nth_base f j < i → j < \len f →
    (∀n.n<j → nth_base f n < i) →
    (∀n.j < n → n < \len f → i ≤ nth_base f n) → value_spec f i q. 

definition match_pred ≝
 λi.λx:bar.match q_cmp (Qpos i) (\fst x) with[ q_leq _ ⇒ true| q_gt _ ⇒ false].

definition match_domain ≝
  λf: list bar.λi:ratio. pred (find ? (match_pred i) f ▭).
   
definition value_simple ≝
  λf: list bar.λi:ratio. nth_height f (match_domain f i).
         
alias symbol "lt" (instance 5) = "Q less than".
alias symbol "lt" (instance 6) = "natural 'less than'".
definition value_lemma : 
  ∀f:list bar.sorted q2_lt f → O < length bar f → 
  ∀i:ratio.nth_base f O  < Qpos i → ∃p:ℚ×ℚ.value_spec f (Qpos i) p.
intros (f bars_sorted_f len_bases_gt_O_f i bars_begin_OQ_f);
exists [apply (value_simple f i);]
apply (value_of ?? (match_domain f i));
[1: reflexivity
|2: unfold match_domain; cases (cases_find bar (match_pred i) f ▭);
    [1: cases i1 in H H1 H2 H3; simplify; intros;
        [1: generalize in match (bars_begin_OQ_f); 
            cases (len_gt_non_empty ?? (len_bases_gt_O_f)); simplify; intros;
            assumption;
        |2: cases (len_gt_non_empty ?? (len_bases_gt_O_f)) in H3;
            intros; lapply (H3 n (le_n ?)) as K; unfold match_pred in K;
            cases (q_cmp (Qpos i) (\fst (\nth (x::l) ▭ n))) in K;
            simplify; intros; [destruct H5] assumption] 
    |2: destruct H; cases (len_gt_non_empty ?? (len_bases_gt_O_f)) in H2;
        simplify; intros; lapply (H (\len l) (le_n ?)) as K; clear H;
        unfold match_pred in K; cases (q_cmp (Qpos i) (\fst (\nth (x::l) ▭ (\len l)))) in K;
        simplify; intros; [destruct H2] assumption;]     
|5: intro; unfold match_domain; cases (cases_find bar (match_pred i) f ▭); intros;
    [1: generalize in match (bars_sorted_f); 
        cases (list_break ??? H) in H1; rewrite > H6;
        rewrite < H1; simplify; rewrite > nth_len; unfold match_pred; 
        cases (q_cmp (Qpos i) (\fst x)); simplify; 
        intros (X Hs); [2: destruct X] clear X;
        cases (sorted_pivot q2_lt ??? ▭ Hs);
        cut (\len l1 ≤ n) as Hn; [2:
          rewrite > H1;  cases i1 in H4; simplify; intro X; [2: assumption]
          apply lt_to_le; assumption;]
        unfold nth_base; rewrite > (nth_append_ge_len ????? Hn);
        cut (n - \len l1 < \len (x::l2)) as K; [2:
          simplify; rewrite > H1; rewrite > (?:\len l2 = \len f - \len (l1 @ [x]));[2:
            rewrite > H6; repeat rewrite > len_append; simplify;
            repeat rewrite < plus_n_Sm; rewrite < plus_n_O; simplify;
            rewrite > sym_plus; rewrite < minus_plus_m_m; reflexivity;]
          rewrite > len_append; rewrite > H1; simplify; rewrite < plus_n_SO;
          apply le_S_S; clear H1 H6 H7 Hs H8 H9 Hn x l2 l1 H4 H3 H2 H;
          elim (\len f) in i1 n H5; [cases (not_le_Sn_O ? H);]
          simplify; cases n2; [ repeat rewrite < minus_n_O; apply le_S_S_to_le; assumption]
          cases n1 in H1; [intros; rewrite > eq_minus_n_m_O; apply le_O_n]
          intros; simplify; apply H; apply le_S_S_to_le; assumption;]
        cases (n - \len l1) in K; simplify; intros; [ assumption]
        lapply (H9 ? (le_S_S_to_le ?? H10)) as W; apply (q_le_trans ??? H7);
        apply q_lt_to_le; apply W;
    |2: cases (not_le_Sn_n i1); rewrite > H in ⊢ (??%);
        apply (trans_le ??? ? H4); cases i1 in H3; intros; apply le_S_S; 
        [ apply le_O_n; | assumption]]
|3: unfold match_domain; cases (cases_find bar (match_pred i) f ▭); [
      cases i1 in H; intros; simplify; [assumption]
      apply lt_S_to_lt; assumption;]
    rewrite > H; cases (\len f) in len_bases_gt_O_f; intros; [cases (not_le_Sn_O ? H3)]
    simplify; apply le_n;
|4: intros; unfold match_domain in H; cases (cases_find bar (match_pred i) f ▭) in H; simplify; intros; 
    [1: lapply (H3 n); [2: cases i1 in H4; intros [assumption] apply le_S; assumption;]
        unfold match_pred in Hletin; cases (q_cmp (Qpos i) (\fst (\nth f ▭ n))) in Hletin;
        simplify; intros; [destruct H6] assumption;
    |2: destruct H; cases f in len_bases_gt_O_f H2 H3; clear H1; simplify; intros;
        [cases (not_le_Sn_O ? H)] lapply (H1 n); [2: apply le_S; assumption]
        unfold match_pred in Hletin; cases (q_cmp (Qpos i) (\fst (\nth (b::l) ▭ n))) in Hletin;
        simplify; intros; [destruct H4] assumption;]]
qed.    

lemma bars_begin_lt_Qpos : ∀q,r. nth_base (bars q) O<Qpos r.
intros; rewrite > bars_begin_OQ; apply q_pos_OQ;
qed.

lemma value : q_f → ratio → ℚ × ℚ.
intros; cases (value_lemma (bars q) ?? r); 
[ apply bars_sorted.
| apply len_bases_gt_O;
| apply w; 
| apply bars_begin_lt_Qpos;]
qed.

lemma cases_value : ∀f,i. value_spec (bars f) (Qpos i) (value f i).
intros; unfold value; 
cases (value_lemma (bars f) (bars_sorted f) (len_bases_gt_O f) i (bars_begin_lt_Qpos f i)); 
assumption;
qed.

definition same_values ≝ λl1,l2:q_f.∀input. value l1 input = value l2 input. 

definition same_bases ≝ λl1,l2:list bar. ∀i.\fst (\nth l1 ▭ i) = \fst (\nth l2 ▭ i).

lemma same_bases_cons: ∀a,b,l1,l2.
  same_bases l1 l2 → \fst a = \fst b → same_bases (a::l1) (b::l2).
intros; intro; cases i; simplify; [assumption;] apply (H n);
qed.

alias symbol "lt" = "Q less than".
lemma unpos: ∀x:ℚ.OQ < x → ∃r:ratio.Qpos r = x.
intro; cases x; intros; [2:exists [apply r] reflexivity]
cases (?:False);
[ apply (q_lt_corefl ? H)| cases (q_lt_le_incompat ?? (q_neg_gt ?) (q_lt_to_le ?? H))]
qed.

notation < "x \blacksquare" non associative with precedence 55 for @{'unpos $x}.
interpretation "hide unpos proof" 'unpos x = (unpos x ?).

