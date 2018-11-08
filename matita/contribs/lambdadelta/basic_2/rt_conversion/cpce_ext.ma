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
include "basic_2/rt_conversion/cpce.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR BINDERS ********************)

definition cpce_ext (h) (G): relation3 lenv bind bind ≝ cext2 (cpce h G).

interpretation
  "context-sensitive parallel eta-conversion (binder)"
  'PConvEta h G L I1 I2 = (cpce_ext h G L I1 I2).
