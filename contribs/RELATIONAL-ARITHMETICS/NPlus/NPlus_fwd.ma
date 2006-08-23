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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/fwd".

include "Nat/Nat_fwd.ma".
include "NPlus/NPlus.ma".

(* primitive generation lemmas proved by elimination and inversion *)

theorem nplus_gen_zero_1: \forall q,r. NPlus zero q r \to q = r.
 intros. elim H; clear H q r; intros;
 [ reflexivity
 | clear H1. auto
 ].
qed.

theorem nplus_gen_succ_1: \forall p,q,r. NPlus (succ p) q r \to 
                          \exists s. r = (succ s) \land NPlus p q s.
 intros. elim H; clear H q r; intros;
 [
 | clear H1.
   decompose.
   rewrite > H1. clear H1 n2
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem nplus_gen_zero_2: \forall p,r. NPlus p zero r \to p = r.
 intros. inversion H; clear H; intros;
 [ auto
 | clear H H1.
   lapply eq_gen_zero_succ to H2 as H0. apply H0
 ].
qed.

theorem nplus_gen_succ_2: \forall p,q,r. NPlus p (succ q) r \to 
                          \exists s. r = (succ s) \land NPlus p q s.
 intros. inversion H; clear H; intros;
 [ lapply eq_gen_succ_zero to H as H0. apply H0
 | clear H1 H3 r.
   lapply linear eq_gen_succ_succ to H2 as H0.
   rewrite > H0. clear H0 q.
   apply ex_intro; [| auto ] (**)
 ].
qed.

theorem nplus_gen_zero_3: \forall p,q. NPlus p q zero \to p = zero \land q = zero.
 intros. inversion H; clear H; intros;
 [ rewrite < H1. clear H1 p.
   auto
 | clear H H1.
   lapply eq_gen_zero_succ to H3 as H0. apply H0
 ].
qed.

theorem nplus_gen_succ_3: \forall p,q,r. NPlus p q (succ r) \to
                          \exists s. p = succ s \land NPlus s q r \lor
                                     q = succ s \land NPlus p s r.
 intros. inversion H; clear H; intros;
 [ rewrite < H1. clear H1 p
 | clear H1.
   lapply linear eq_gen_succ_succ to H3 as H0.
   rewrite > H0. clear H0 r.
 ]; apply ex_intro; [| auto || auto ] (**)
qed.
(*
(* alternative proofs invoking nplus_gen_2 *)

variant nplus_gen_zero_3_alt: \forall p,q. NPlus p q zero \to p = zero \land q = zero.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p.
   auto
 | clear H.
   lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   lapply linear eq_gen_zero_succ to H1 as H0. apply H0
 ].
qed.

variant nplus_gen_succ_3_alt: \forall p,q,r. NPlus p q (succ r) \to
                              \exists s. p = succ s \land NPlus s q r \lor
                                         q = succ s \land NPlus p s r.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p
 | clear H.
   lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   lapply linear eq_gen_succ_succ to H1 as H0.
   rewrite > H0. clear H0 r.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.
*)
(* other simplification lemmas *)

theorem nplus_gen_eq_2_3: \forall p,q. NPlus p q q \to p = zero.
 intros 2. elim q; clear q; intros;
 [ lapply linear nplus_gen_zero_2 to H as H0.
   rewrite > H0. clear H0 p
 | lapply linear nplus_gen_succ_2 to H1 as H0.
   decompose.
   lapply linear eq_gen_succ_succ to H2 as H0.
   rewrite < H0 in H3. clear H0 a
 ]; auto.
qed.

theorem nplus_gen_eq_1_3: \forall p,q. NPlus p q p \to q = zero.
 intros 1. elim p; clear p; intros;
 [ lapply linear nplus_gen_zero_1 to H as H0.
   rewrite > H0. clear H0 q
 | lapply linear nplus_gen_succ_1 to H1 as H0.
   decompose.
   lapply linear eq_gen_succ_succ to H2 as H0.
   rewrite < H0 in H3. clear H0 a
 ]; auto.
qed.
