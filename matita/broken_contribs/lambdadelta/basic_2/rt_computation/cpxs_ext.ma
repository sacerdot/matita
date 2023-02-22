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

include "static_2/syntax/cext2.ma".
include "basic_2/rt_computation/cpxs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR BINDERS ***********)

definition cpxs_ext (G): relation3 lenv bind bind ≝
           cext2 (cpxs G).

interpretation
  "extended context-sensitive parallel rt-computation (binder)"
  'PRedTyStar G L I1 I2 = (cpxs_ext G L I1 I2).
