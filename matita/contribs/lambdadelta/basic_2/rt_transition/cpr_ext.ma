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

include "basic_2/syntax/cext2.ma".
include "basic_2/rt_transition/cpm.ma".

(* CONTEXT-SENSITIVE PARALLEL R-TRANSITION FOR BINDERS **********************)

definition cpr_ext (h) (G): relation3 lenv bind bind ≝
                            cext2 (cpm 0 h G).

interpretation
   "context-sensitive parallel r-transition (binder)"
   'PRed h G L I1 I2 = (cpr_ext h G L I1 I2).
