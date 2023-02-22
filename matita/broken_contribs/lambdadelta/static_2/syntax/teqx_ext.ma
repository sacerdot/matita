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

(*
include "static_2/notation/relations/approxeq_3.ma".
*)
include "static_2/syntax/teqg_ext.ma".
include "static_2/syntax/teqx.ma".

(* EXTENDED SORT-IRRELEVANT EQUIVALENCE *************************************)
(*
definition teqx_ext: relation bind ≝
           teqg_ext sfull.

definition ceqx: relation3 lenv term term ≝
           ceqg sfull.
*)
definition ceqx_ext: relation3 lenv bind bind ≝
           ceqg_ext sfull.
(*
interpretation
  "context-free sort-irrelevant equivalence (binder)"
  'StarEq I1 I2 = (teqx_ext I1 I2).

interpretation
  "context-dependent sort-irrelevant equivalence (term)"
  'StarEq L T1 T2 = (cdeq L T1 T2).

interpretation
  "context-dependent sort-irrelevant equivalence (binder)"
  'ApproxEq L I1 I2 = (cdeq_ext L I1 I2).
*)
