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

include "nat/exp.ma".
include "nat/relevant_equations.ma".

alias num (instance 0) = "natural number".

theorem plus_inv_O3: ∀m,n. 0 = n + m → 0 = n ∧ 0 = m.
 intros 2; elim n names 0; clear n; simplify; intros;
 [ autobatch | destruct ].
qed. 

theorem times_inv_O3_S: ∀x,y. 0 = x * (S y) → x = 0.
 intros; rewrite < times_n_Sm in H;
 lapply linear plus_inv_O3 to H; decompose;autobatch.
qed. 

theorem not_3_divides_1: ∀n. 1 = n * 3 → False.
 intros 1; rewrite > sym_times; simplify;
 elim n names 0; simplify; intros; destruct;
 rewrite > sym_plus in Hcut; simplify in Hcut; destruct Hcut.
qed.

variant le_inv_S_S: ∀m,n. S m ≤ S n → m ≤ n 
≝ le_S_S_to_le.

theorem plus_inv_S_S_S: ∀x,y,z. S x = S y + S z → S y ≤ x ∧ S z ≤ x.
 simplify; intros; destruct;autobatch.
qed.

theorem times_inv_S_m_SS: ∀k,n,m. S n = m * (S (S k)) → m ≤ n.
 intros 3; elim m names 0; clear m; simplify; intros; destruct;
 clear H; autobatch by le_S_S, transitive_le, le_plus_n, le_plus_n_r. 
qed.

theorem plus_3_S3n: ∀n. S (S n * 3) = 3 + S (n * 3).
 intros; autobatch depth = 1.
qed. 

theorem times_exp_x_y_Sz: ∀x,y,z. x * y \sup (S z) = (x * y \sup z) * y.
 intros; autobatch depth = 1.
qed.

definition acc_nat: (nat → Prop) → nat →Prop ≝
   λP:nat→Prop. λn. ∀m. m ≤ n → P m.

theorem wf_le: ∀P. P 0 → (∀n. acc_nat P n → P (S n)) → ∀n. acc_nat P n.
 unfold acc_nat; intros 4; elim n names 0; clear n;
 [ intros; autobatch by (eq_ind ? ? P), H, H2, le_n_O_to_eq.
   (* lapply linear le_n_O_to_eq to H2; destruct; autobatch *)
 | intros 3; elim m; clear m; intros; clear H3;
   [ clear H H1; autobatch depth = 2
   | clear H; lapply linear le_inv_S_S to H4;
     apply H1; clear H1; intros;
     apply H2; clear H2; autobatch depth = 2
   ]
 ].
qed.

theorem wf_nat_ind: 
   ∀P:nat→Prop. P O → (∀n. (∀m. m ≤ n → P m) → P (S n)) → ∀n. P n.
 intros; lapply linear depth=2 wf_le to H, H1 as H0; 
  autobatch. 
qed.
