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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICsucc/Plus_props".

include "Plus_fwd.ma".

theorem Plus_zero_1: \forall q. Plus zero q q.
 intros. elim q; clear q; auto.
qed.

theorem Plus_succ_1: \forall p,q,r. Plus p q r \to Plus (succ p) q (succ r).
 intros 2. elim q; clear q;
 [ lapply linear Plus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p
 | lapply linear Plus_gen_succ_2 to H1 as H0.
   decompose.
   rewrite > H2. clear H2 r
 ]; auto.
qed.

theorem Plus_sym: \forall p,q,r. Plus p q r \to Plus q p r.
 intros 2. elim q; clear q;
 [ lapply linear Plus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p
 | lapply linear Plus_gen_succ_2 to H1 as H0.
   decompose.
   rewrite > H2. clear H2 r
 ]; auto.
qed.

theorem Plus_shift_succ_sx: \forall p,q,r. 
                            Plus p (succ q) r \to Plus (succ p) q r.
 intros.
 lapply linear Plus_gen_succ_2 to H as H0.
 decompose.
 rewrite > H1. clear H1 r.
 auto.
qed.

theorem Plus_shift_succ_dx: \forall p,q,r. 
                            Plus (succ p) q r \to Plus p (succ q) r.
 intros.
 lapply linear Plus_gen_succ_1 to H as H0.
 decompose.
 rewrite > H1. clear H1 r.
 auto.
qed.

theorem Plus_trans_1: \forall p,q1,r1. Plus p q1 r1 \to 
                      \forall q2,r2. Plus r1 q2 r2 \to
                      \exists q. Plus q1 q2 q \land Plus p q r2.
 intros 2; elim q1; clear q1; intros;
 [ lapply linear Plus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p
 | lapply linear Plus_gen_succ_2 to H1 as H0.
   decompose.
   rewrite > H3. rewrite > H3 in H2. clear H3 r1.
   lapply linear Plus_gen_succ_1 to H2 as H0.
   decompose.
   rewrite > H2. clear H2 r2.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem Plus_trans_2: \forall p1,q,r1. Plus p1 q r1 \to 
                      \forall p2,r2. Plus p2 r1 r2 \to
                      \exists p. Plus p1 p2 p \land Plus p q r2.
 intros 2; elim q; clear q; intros;
 [ lapply linear Plus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p1
 | lapply linear Plus_gen_succ_2 to H1 as H0.
   decompose.
   rewrite > H3. rewrite > H3 in H2. clear H3 r1.
   lapply linear Plus_gen_succ_2 to H2 as H0.
   decompose.
   rewrite > H2. clear H2 r2.
   lapply linear H to H4, H3 as H0.
   decompose.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem Plus_conf: \forall p,q,r1. Plus p q r1 \to 
                   \forall r2. Plus p q r2 \to r1 = r2.
 intros 2. elim q; clear q; intros;
 [ lapply linear Plus_gen_zero_2 to H as H0.
   rewrite > H0 in H1. clear H0 p
 | lapply linear Plus_gen_succ_2 to H1 as H0.
   decompose.
   rewrite > H3. clear H3 r1.
   lapply linear Plus_gen_succ_2 to H2 as H0.
   decompose.
   rewrite > H2. clear H2 r2.
 ]; auto.
qed.
