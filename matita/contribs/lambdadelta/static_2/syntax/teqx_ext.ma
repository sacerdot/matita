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

include "static_2/notation/relations/stareq_3.ma".
include "static_2/syntax/cext2.ma".
include "static_2/syntax/teqx.ma".

(* EXTENDED SORT-IRRELEVANT EQUIVALENCE *************************************)

definition teqx_ext: relation bind ≝
                     ext2 teqx.

definition cdeq: relation3 lenv term term ≝
                 λL. teqx.

definition cdeq_ext: relation3 lenv bind bind ≝
                     cext2 cdeq.

interpretation
   "context-free sort-irrelevant equivalence (binder)"
   'StarEq I1 I2 = (teqx_ext I1 I2).

interpretation
   "context-dependent sort-irrelevant equivalence (term)"
   'StarEq L T1 T2 = (cdeq L T1 T2).

interpretation
   "context-dependent sort-irrelevant equivalence (binder)"
   'StarEq L I1 I2 = (cdeq_ext L I1 I2).
