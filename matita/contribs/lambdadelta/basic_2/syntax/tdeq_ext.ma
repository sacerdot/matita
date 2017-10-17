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

include "basic_2/syntax/tdeq.ma".
include "basic_2/syntax/lenv_ext2.ma".

(* EXTENDED DEGREE-BASED EQUIVALENCE ****************************************)

definition cdeq: ∀h. sd h → relation3 lenv term term ≝
                 λh,o,L. tdeq h o.

definition tdeq_ext: ∀h. sd h → relation bind ≝
                     λh,o. ext2 (tdeq h o).

definition cdeq_ext: ∀h. sd h → relation3 lenv bind bind ≝
                     λh,o. cext2 (cdeq h o).

interpretation
   "degree-based equivalence (binder)"
   'LazyEq h o I1 I2 = (tdeq_ext h o I1 I2).
