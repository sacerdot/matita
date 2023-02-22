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
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR BINDERS *********************)

definition cprs_ext (h) (n) (G): relation3 lenv bind bind ≝
           cext2 (λL. cpms h G L n).

interpretation
   "context-sensitive parallel r-computation (binder)"
   'PRedStar h n G L I1 I2 = (cprs_ext h n G L I1 I2).
