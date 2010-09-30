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

include "dama/models/nat_uniform.ma".
include "dama/supremum.ma".
include "nat/le_arith.ma".
include "dama/russell_support.ma".

lemma hint1:
 ∀s.sequence (Type_of_ordered_set (segment_ordered_set nat_ordered_set s))
   → sequence (hos_carr (os_l (segment_ordered_set nat_ordered_set s))).
intros; assumption;
qed.   
   
coercion hint1 nocomposites.   
   
alias symbol "pi1" = "exT \fst".
alias symbol "N" = "ordered set N".
alias symbol "dependent_pair" = "dependent pair".
lemma increasing_supremum_stabilizes:
  ∀sg:‡ℕ.∀a:sequence {[sg]}.
   a is_increasing → 
    ∀X.X is_supremum a → ∃i.∀j.i ≤ j → \fst X = \fst (a j).
intros 4; cases X (x Hx); clear X; letin X ≝ ≪x,Hx≫; 
fold normalize X; intros; cases H1; 
alias symbol "N" = "Natural numbers".
letin spec ≝ (λi,j:ℕ.(𝕦_ sg ≤ i ∧ x = \fst (a j)) ∨ (i < 𝕦_ sg ∧ x + i ≤ 𝕦_ sg + \fst (a j))); 
(* x - aj <= max 0 (u - i) *)  
letin m ≝ (hide ? (
  let rec aux i ≝
    match i with
    [ O ⇒ O
    | S m ⇒ 
        let pred ≝ aux m in
        let apred ≝ a pred in 
        match cmp_nat x (\fst apred) with
        [ cmp_le _ ⇒ pred
        | cmp_gt nP ⇒ \fst (H3 apred ?)]]
  in aux 
   :
   ∀i:nat.∃j:nat.spec i j));[whd; apply nP;] unfold spec in aux ⊢ %;
[3: unfold X in H2; clear H4 n aux spec H3 H1 H X;
    cases (cases_in_segment ??? Hx);
    elim 𝕦_ sg in H1 ⊢ %; intros (a Hs H);
    [1: left; split; [apply le_n]
        generalize in match H;
        generalize in match Hx;
        rewrite > (?:x = O); 
        [2: cases Hx; lapply (os_le_to_nat_le ?? H1);
            apply (symmetric_eq nat O x ?).apply (le_n_O_to_eq x ?).apply (Hletin).
        |1: intros; unfold Type_OF_ordered_set in sg a; whd in a:(? %);
            lapply (H2 O) as K; lapply (sl2l_ ?? (a O) ≪x,Hx≫ K) as P;
            simplify in P:(???%); lapply (le_transitive ??? P H1) as W;
            lapply (os_le_to_nat_le ?? W) as R; apply (le_n_O_to_eq (\fst (a O)) R);]
    |2: right; cases Hx; rewrite > (sym_plus x O); split; [apply le_S_S; apply le_O_n];
        apply (trans_le ??? (os_le_to_nat_le ?? H3));
        apply le_plus_n_r;] 
|2: clear H6; cut (x = \fst (a (aux n1))); [2:
      cases (le_to_or_lt_eq ?? H5); [2: assumption]
      cases (?:False); apply (H2 (aux n1) H6);] clear H5;
      generalize in match Hcut; clear Hcut; intro H5;
|1: clear H6]
[2,1:
    cases (aux n1) in H5 ⊢ %; intros;
    change in match (a ≪w,H5≫) in H6 ⊢ % with (a w);
    cases H5; clear H5; cases H7; clear H7;
    [1: left; split; [ apply (le_S ?? H5); | assumption]
    |3: cases (?:False); rewrite < H8 in H6; apply (not_le_Sn_n ? H6);
    |*: cases (cmp_nat 𝕦_ sg (S n1));
        [1,3: left; split; [1,3: assumption |2: assumption]
            cut (𝕦_ sg = S n1); [2: apply le_to_le_to_eq; assumption ]
            clear H7 H5 H4;rewrite > Hcut in H8:(? ? (? % ?)); clear Hcut;
            cut (x = S (\fst (a w)));
            [2: apply le_to_le_to_eq; [2: assumption]
                change in H8 with (x + n1 ≤ S (n1 + \fst (a w)));
                rewrite > plus_n_Sm in H8; rewrite > sym_plus in H8;
                apply (le_plus_to_le ??? H8);]
            cases (H3 (a w) H6);
            change with (x = \fst (a w1));
            change in H4 with (\fst (a w) < \fst (a w1));
            apply le_to_le_to_eq; [ rewrite > Hcut; assumption ]
            apply (os_le_to_nat_le (\fst (a w1)) x (H2 w1));
        |*: right; split; try assumption;
            [1: rewrite > sym_plus in ⊢ (? ? %);
                rewrite < H6; apply le_plus_r; assumption;
            |2: cases (H3 (a w) H6);
                change with (x + S n1 ≤ 𝕦_ sg + \fst (a w1));rewrite < plus_n_Sm;
                apply (trans_le ??? (le_S_S ?? H8)); rewrite > plus_n_Sm;
                apply (le_plus ???? (le_n ?) H9);]]]]
clearbody m; unfold spec in m; clear spec;
alias symbol "exists" = "CProp exists".
letin find ≝ (
 let rec find i u on u : nat ≝
  match u with
  [ O ⇒ (m i:nat)
  | S w ⇒ match eqb (\fst (a (m i))) x with
          [ true ⇒ (m i:nat)
          | false ⇒ find (S i) w]]
 in find
 :
  ∀i,bound.∃j.i + bound = 𝕦_ sg → x = \fst (a j));
[1: cases (find (S n) n2); intro; change with (x = \fst (a w));
    apply H6; rewrite < H7; simplify; apply plus_n_Sm;
|2: intros; rewrite > (eqb_true_to_eq ?? H5); reflexivity
|3: intros; rewrite > sym_plus in H5; rewrite > H5; clear H5 H4 n n1;
    cases (m 𝕦_ sg); cases H4; clear H4; cases H5; clear H5; [assumption]
    cases (not_le_Sn_n ? H4)]
clearbody find; cases (find O 𝕦_ sg);
exists [apply w]; intros; change with (x = \fst (a j));
rewrite > (H4 ?); [2: reflexivity]
apply le_to_le_to_eq;
[1: apply os_le_to_nat_le;
    apply (trans_increasing a H ? ? (nat_le_to_os_le ?? H5));
|2: apply (trans_le ? x ?);[apply os_le_to_nat_le; apply (H2 j);]
    rewrite < (H4 ?); [2: reflexivity] apply le_n;]
qed.

lemma hint2:
 ∀s.sequence (Type_of_ordered_set (segment_ordered_set nat_ordered_set s))
   → sequence (hos_carr (os_r (segment_ordered_set nat_ordered_set s))).
intros; assumption;
qed.   
   
coercion hint2 nocomposites.   
   
alias symbol "N" = "ordered set N".
axiom increasing_supremum_stabilizes_r:
  ∀s:‡ℕ.∀a:sequence {[s]}.a is_decreasing → 
    ∀x.x is_infimum a → ∃i.∀j.i ≤ j → \fst x = \fst (a j).
