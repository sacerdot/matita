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

include "classes/defs.ma".

theorem p_inv_O: P 0 → False.
 intros; inversion H;intros;
 [apply (not_eq_O_S ? H1)
 |autobatch.
 ]
qed.

theorem t_inv_O: T 0 → False.
 intros; inversion H; clear H; intros;
 [ lapply linear times_inv_O3_S to H1; destruct; autobatch depth = 2
 | lapply linear times_inv_O3_S to H2; destruct; autobatch depth = 2
 ].
qed.

theorem p_pos: ∀i. P i → ∃k. i = S k.
 intros 1; elim i 0; clear i; intros;
 [ lapply linear p_inv_O to H; decompose
 | autobatch depth = 2
 ].
qed.

theorem t_pos: ∀i. T i → ∃k. i = S k.
 intros 1; elim i names 0; clear i; intros;
 [ lapply linear t_inv_O to H; decompose
 | autobatch depth = 2
 ].
qed.

theorem t_1: T 1 → False.
 intros; inversion H; clear H; intros;
 [ lapply not_3_divides_1 to H1; decompose
 | lapply not_3_divides_1 to H2; decompose
 ].
qed.

theorem t_3: T 3.
 change in ⊢ (? %) with (1 * 3);
 autobatch depth = 2.
qed.

theorem pt_inv_gen: ∀i. 
                    (P i → ∃h. i = S (h * 3)) ∧
                    (T i → ∃h,k. i = S (h * 3) * 3 \sup (S k)).
 intros 1; elim i using wf_nat_ind names 0; clear i; intros; split; intros;
 [ lapply linear p_inv_O to H; decompose
 | lapply linear t_inv_O to H; decompose
 | inversion H1; clear H1; intros;
   [ destruct; autobatch paramodulation
   | clear H3; lapply t_pos to H1; lapply p_pos to H2; decompose; destruct;
     lapply linear plus_inv_S_S_S to H4; decompose;
     lapply H to H4; lapply H to H3; clear H H4 H3; decompose; clear H3 H4;
     lapply linear H to H2; lapply linear H5 to H1; decompose;
     rewrite > H; rewrite > H2; clear H H2;
     rewrite < plus_n_Sm; rewrite > times_exp_x_y_Sz; autobatch depth = 2
   ]
 | inversion H1; clear H1; intros;
   [ lapply linear times_inv_S_m_SS to H2 as H0;
     lapply linear H to H0; decompose; clear H2;
     lapply linear H to H1; decompose; destruct;
     autobatch depth = 4
   | clear H2; lapply linear times_inv_S_m_SS to H3 as H0;
     lapply linear H to H0; decompose; clear H;
     lapply linear H2 to H1; decompose; destruct;
     autobatch depth = 4
   ]
 ].
qed.

theorem p_inv_gen: ∀i. P i → ∃h. i = S (h * 3).
 intros; lapply depth = 1 pt_inv_gen; decompose;
 lapply linear H1 to H as H0; autobatch depth = 1.
qed.

theorem t_inv_gen: ∀i. T i → ∃h,k. i = (S (h * 3)) * 3 \sup (S k).
 intros; lapply depth = 1 pt_inv_gen; decompose;
 lapply linear H2 to H as H0; autobatch depth = 2.
qed.

theorem p_gen: ∀i. P (S (i * 3)).
 intros; elim i names 0; clear i; intros;
 [ simplify; autobatch depth = 2
 | rewrite > plus_3_S3n ; autobatch depth = 2
 ].
qed.

theorem t_gen: ∀i,j. T (S (i * 3) * 3 \sup (S j)).
 intros; elim j names 0; clear j; intros;
 [ simplify in ⊢ (? (? ? %)); autobatch depth = 2
 | rewrite > times_exp_x_y_Sz; autobatch depth = 2
 ].
qed.
