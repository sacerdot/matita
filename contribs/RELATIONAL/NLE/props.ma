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

theorem nle_refl: \forall x. x <= x.
 intros 1; elim x; clear x; intros; auto new.
qed.

theorem nle_trans_succ: \forall x,y. x <= y \to x <= succ y.
 intros. elim H; clear H x y; intros; auto new.
qed.

theorem nle_lt_or_eq: \forall y,x. x <= y \to x < y \lor x = y.
 intros 1. elim y; clear y; intros;
 [ lapply linear nle_gen_zero_2 to H. auto new
 | lapply linear nle_gen_succ_2 to H1. decompose;
   [ subst. auto new
   | lapply linear H to H3 as H0. decompose;
     subst; auto new
   ]
 ].
qed.
