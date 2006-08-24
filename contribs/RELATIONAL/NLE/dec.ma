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

set "baseuri" "cic:/matita/RELATIONAL/NLE/dec".

include "NLE/props.ma".

theorem nat_dec_lt_ge: \forall x,y. x < y \lor y <= x.
 intros 2; elim y; clear y;
 [ auto
 | decompose;
   [ lapply linear nle_gen_succ_1 to H1. decompose.
     rewrite > H1. clear H1 n. auto
   | lapply linear nle_lt_or_eq to H1; decompose;
     [ auto
     | rewrite > H. clear H n. auto
     ]
   ]
 ].
qed.
