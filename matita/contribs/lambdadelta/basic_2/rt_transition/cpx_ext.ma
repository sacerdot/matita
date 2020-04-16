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
include "basic_2/rt_transition/cpx.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR BINDERS ************)

definition cpx_ext (G): relation3 lenv bind bind ≝
           cext2 (cpx G).

interpretation
  "extended context-sensitive parallel rt-transition (binder)"
  'PRedTy G L I1 I2 = (cpx_ext G L I1 I2).
