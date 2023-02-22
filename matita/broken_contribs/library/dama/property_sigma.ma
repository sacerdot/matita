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

include "dama/ordered_uniform.ma".
include "dama/russell_support.ma".

(* Definition 3.5 *)
alias num (instance 0) = "natural number".
definition property_sigma ≝
  λC:ordered_uniform_space.
   ∀U.us_unifbase ? U → 
     ∃V:sequence (C squareB → Prop).
       (∀i.us_unifbase ? (V i)) ∧ 
       ∀a:sequence C.∀x:C.(a ↑ x ∨ a ↓ x) → 
         (∀n.∀i,j.n ≤ i → n ≤ j → V n 〈a i,a j〉) → U 〈a 0,x〉.
      
definition max ≝
  λm,n.match leb n m with [true ⇒ m | false ⇒ n].
  
lemma le_max: ∀n,m.m ≤ max n m.
intros; unfold max; apply leb_elim; simplify; intros; [assumption] apply le_n;
qed.

lemma max_le_l: ∀n,m,z.max n m ≤ z → n ≤ z.
intros 3; unfold max; apply leb_elim; simplify; intros; [assumption]
apply lt_to_le; apply (lt_to_le_to_lt ???? H1);
apply not_le_to_lt; assumption;
qed.

lemma sym_max: ∀n,m.max n m = max m n.
intros; apply (nat_elim2 ???? n m); simplify; intros;
[1: elim n1; [reflexivity] rewrite < H in ⊢ (? ? ? (? %));
    simplify; rewrite > H; reflexivity;
|2: reflexivity
|3: apply leb_elim; apply leb_elim; simplify;
    [1: intros; apply le_to_le_to_eq; apply le_S_S;assumption;
    |2,3: intros; reflexivity;
    |4: intros; unfold max in H; 
        rewrite > (?:leb n1 m1 = false) in H; [2:
          apply lt_to_leb_false; apply not_le_to_lt; assumption;]
        rewrite > (?:leb m1 n1 = false) in H; [2:
          apply lt_to_leb_false; apply not_le_to_lt; assumption;]
        apply eq_f; assumption;]]
qed.

lemma max_le_r: ∀n,m,z.max n m ≤ z → m ≤ z.
intros; rewrite > sym_max in H; apply (max_le_l ??? H); 
qed.
  
(* Lemma 3.6 *)   
lemma sigma_cauchy:
  ∀C:ordered_uniform_space.property_sigma C →
    ∀a:sequence C.∀l:C.(a ↑ l ∨ a ↓ l) → a is_cauchy → a uniform_converges l.
intros 8; cases (H ? H3) (w H5); cases H5 (H8 H9); clear H5;
letin spec ≝ (λz,k:nat.∀i,j,l:nat.k ≤ i → k ≤ j → l ≤ z → w l 〈a i,a j〉);
letin m ≝ (hide ? (let rec aux (i:nat) : nat ≝
  match i with
  [ O ⇒ match H2 (w i) ? with [ ex_introT k _ ⇒ k ]
  | S i' ⇒ max (match H2 (w i) ? with [ ex_introT k _ ⇒ k ]) (S (aux i'))
  ] in aux
  : ∀z.∃k. spec z k)); unfold spec in aux ⊢ %;
  [1,2:apply H8;
  |3: intros 3; cases (H2 (w n) (H8 n)); simplify in ⊢ (? (? % ?) ?→?);
      simplify in ⊢ (?→? (? % ?) ?→?);
      intros; lapply (H5 i j) as H14;
        [2: apply (max_le_l ??? H6);|3:apply (max_le_l ??? H7);]
      cases (le_to_or_lt_eq ?? H10); [2: destruct H11; destruct H4; assumption]
      cases (aux n1) in H6 H7 ⊢ %; simplify in ⊢ (? (? ? %) ?→? (? ? %) ?→?); intros;
      apply H6; [3: apply le_S_S_to_le; assumption]
      apply lt_to_le; apply (max_le_r w1); assumption;
  |4: intros; clear H6; rewrite > H4 in H5; 
      rewrite < (le_n_O_to_eq ? H11); apply H5; assumption;] 
cut ((⌊x,(m x:nat)⌋ : sequence nat_ordered_set) is_strictly_increasing) as Hm; [2:
  intro n; change with (S (m n) ≤ m (S n)); unfold m; 
  whd in ⊢ (? ? %); apply (le_max ? (S (m n)));]
cut ((⌊x,(m x:nat)⌋ : sequence nat_ordered_set) is_increasing) as Hm1; [2:
  intro n; intro L; change in L with (m (S n) < m n);
  lapply (Hm n) as L1; change in L1 with (m n < m (S n));
  lapply (trans_lt ??? L L1) as L3; apply (not_le_Sn_n ? L3);] 
clearbody m; unfold spec in m Hm Hm1; clear spec;
cut (⌊x,a (m x)⌋ ↑ l ∨ ⌊x,a (m x)⌋ ↓ l) as H10; [2: 
 cases H1;
 [ left; apply (selection_uparrow ? Hm a l H4);
 | right; apply (selection_downarrow ? Hm a l H4);]] 
lapply (H9 ?? H10) as H11; [
  exists [apply (m 0:nat)] intros;
  cases H1; cases H5; cases H7; cases (us_phi4 ?? H3 〈l,a i〉);
  apply H15; change with (U 〈a i,l〉);
    [apply (ous_convex_l C ? H3 ? H11 (H12 (m O)));
    |apply (ous_convex_r C ? H3 ? H11 (H12 (m O)));]
  [1:apply (H12 i);
  |3: apply (le_reflexive l);
  |4: apply (H12 i);
  |2:change with (a (m O) ≤ a i);
     apply (trans_increasing a H6 (\fst (m 0)) i); intro; apply (le_to_not_lt ?? H4 H16);
  |5:apply (H12 i);
  |7:apply (ge_reflexive (l : hos_carr (os_r C)));
  |8:apply (H12 i);
  |6:change with (a i ≤ a (m O));
     apply (trans_decreasing a H6 (\fst (m 0)) i); intro; apply (le_to_not_lt ?? H4 H16);]]  
clear H10; intros (p q r); change with (w p 〈a (m q),a (m r)〉);
generalize in match (refl_eq nat (m p)); 
generalize in match (m p) in ⊢ (? ? ? % → %); intro X; cases X (w1 H15); clear X; 
intros (H16); simplify in H16:(? ? ? %); destruct H16;
apply H15; [3: apply le_n]
[1: lapply (trans_increasing ? Hm1 p q) as T; [apply not_lt_to_le; apply T;]
    apply (le_to_not_lt p q H4);
|2: lapply (trans_increasing ? Hm1 p r) as T; [apply not_lt_to_le; apply T;]
    apply (le_to_not_lt p r H5);]
qed.
