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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICS/add_gen".

include "nat_gen.ma".
include "add_defs.ma".

(* primitive generation lemmas proved by elimination and inversion *)

theorem add_gen_O_1: \forall q,r. add O q r \to q = r.
  intros. elim H; clear H; clear q; clear r; intros;
 [ reflexivity
 | clear H1. auto
 ].
qed.

theorem add_gen_S_1: \forall p,q,r. add (S p) q r \to 
                     \exists s. r = (S s) \land add p q s.
 intros. elim H; clear H; clear q; clear r; intros;
 [
 | clear H1. 
  decompose H2.
  rewrite > H1. clear H1. clear n2
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.

theorem add_gen_O_2: \forall p,r. add p O r \to p = r.
 intros. inversion H; clear H; intros;
 [ auto
 | clear H. clear H1.
   lapply eq_gen_O_S to H2 as H0. apply H0
 ].
qed.

theorem add_gen_S_2: \forall p,q,r. add p (S q) r \to 
                     \exists s. r = (S s) \land add p q s.
 intros. inversion H; clear H; intros;
 [ lapply eq_gen_S_O to H as H0. apply H0
 | clear H1. clear H3. clear r.
   lapply eq_gen_S_S to H2 as H0. clear H2.
   rewrite > H0. clear H0. clear q.
   apply ex_intro; [| auto ] (**)
 ].
qed.

theorem add_gen_O_3: \forall p,q. add p q O \to p = O \land q = O.
 intros. inversion H; clear H; intros;
 [ rewrite < H1. clear H1. clear p.
   auto
 | clear H. clear H1.
   lapply eq_gen_O_S to H3 as H0. apply H0
 ].
qed.

theorem add_gen_S_3: \forall p,q,r. add p q (S r) \to
                     \exists s. p = S s \land add s q r \lor
                                q = S s \land add p s r.
 intros. inversion H; clear H; intros;
 [ rewrite < H1. clear H1. clear p
 | clear H1.
   lapply eq_gen_S_S to H3 as H0. clear H3.
   rewrite > H0. clear H0. clear r.
 ]; apply ex_intro; [| auto || auto ] (**)
qed.

(* alternative proofs invoking add_gen_2 *)

variant add_gen_O_3_alt: \forall p,q. add p q O \to p = O \land q = O.
 intros 2. elim q; clear q; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p.
   auto
 | clear H.
   lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   lapply eq_gen_O_S to H1 as H0. apply H0
 ].
qed.

variant add_gen_S_3_alt: \forall p,q,r. add p q (S r) \to
                         \exists s. p = S s \land add s q r \lor
                                    q = S s \land add p s r.
 intros 2. elim q; clear q; intros;
 [ lapply add_gen_O_2 to H as H0. clear H.
   rewrite > H0. clear H0. clear p
 | clear H.
   lapply add_gen_S_2 to H1 as H0. clear H1.
   decompose H0.
   lapply eq_gen_S_S to H1 as H0. clear H1.
   rewrite > H0. clear H0. clear r.
 ]; apply ex_intro; [| auto || auto ]. (**)
qed.
