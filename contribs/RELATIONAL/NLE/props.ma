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

set "baseuri" "cic:/matita/RELATIONAL/NLE/props".

include "NLE/fwd.ma".

theorem nle_zero: \forall q. zero <= q.
 unfold NLE.
 intros. apply ex_intro; auto. (**)
qed.

theorem nle_succ: \forall p,q. p <= q \to succ p <= succ q.
 unfold NLE.
 intros. decompose.
 apply ex_intro; auto. (**)
qed.

theorem nle_refl: \forall x. x <= x.
 intros 1; elim x; clear x; intros; auto new timeout=100.
qed.

theorem nle_trans_succ: \forall x,y. x <= y \to x <= succ y.
 intros 1. elim x; clear x; intros; 
 [ auto new timeout=100.
 | lapply linear nle_gen_succ_1 to H1 as H0. decompose H0. subst.
   auto new timeout=100.
 ].
qed.

theorem nle_lt_or_eq: \forall y,x. x <= y \to x < y \lor x = y.
 intros 1. elim y; clear y; intros;
 [ lapply linear nle_gen_zero_2 to H. auto new timeout=100
 | lapply linear nle_gen_succ_2 to H1. decompose;
   [ subst. auto new timeout=100
   | lapply linear H to H3 as H0. decompose;
     subst; auto new timeout=100
   ]
 ].
qed.
