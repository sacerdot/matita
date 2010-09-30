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



include "NPlus/defs.ma".

(* Inversion lemmas *********************************************************)

theorem nplus_inv_zero_1: ∀q,r. zero ⊕ q ≍ r → q = r.
 intros. elim H; clear H q r; autobatch.
qed.

theorem nplus_inv_succ_1: ∀p,q,r. succ p ⊕ q ≍ r → 
                          ∃s. r = succ s ∧ p ⊕ q ≍ s.
 intros. elim H; clear H q r; intros;
 [ autobatch depth = 3
 | clear H1; decompose; destruct; autobatch depth = 4
 ]
qed.

theorem nplus_inv_zero_2: ∀p,r. p ⊕ zero ≍ r → p = r.
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem nplus_inv_succ_2: ∀p,q,r. p ⊕ succ q ≍ r → 
                          ∃s. r = succ s ∧ p ⊕ q ≍ s.
 intros; inversion H; clear H; intros; destruct.
 autobatch depth = 3.
qed.

theorem nplus_inv_zero_3: ∀p,q. p ⊕ q ≍ zero → 
                          p = zero ∧ q = zero.
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem nplus_inv_succ_3: ∀p,q,r. p ⊕ q ≍ succ r →
                             ∃s. p = succ s ∧ s ⊕ q ≍ r ∨
                               q = succ s ∧ p ⊕ s ≍ r.
 intros; inversion H; clear H; intros; destruct;
 autobatch depth = 4.
qed.

(* Corollaries to inversion lemmas ******************************************)

theorem nplus_inv_succ_2_3: ∀p,q,r.
                            p ⊕ succ q ≍ succ r → p ⊕ q ≍ r.
 intros;
 lapply linear nplus_inv_succ_2 to H; decompose; destruct; autobatch.
qed.

theorem nplus_inv_succ_1_3: ∀p,q,r.
                            succ p ⊕ q ≍ succ r → p ⊕ q ≍ r.
 intros;
 lapply linear nplus_inv_succ_1 to H; decompose; destruct; autobatch.
qed.

theorem nplus_inv_eq_2_3: ∀p,q. p ⊕ q ≍ q → p = zero.
 intros 2; elim q; clear q;
 [ lapply linear nplus_inv_zero_2 to H
 | lapply linear nplus_inv_succ_2_3 to H1
 ]; autobatch.
qed.

theorem nplus_inv_eq_1_3: ∀p,q. p ⊕ q ≍ p → q = zero.
 intros 1; elim p; clear p;
 [ lapply linear nplus_inv_zero_1 to H
 | lapply linear nplus_inv_succ_1_3 to H1
 ]; autobatch.
qed.
