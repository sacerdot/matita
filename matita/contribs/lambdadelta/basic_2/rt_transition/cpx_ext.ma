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

include "basic_2/syntax/lenv_ext2.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR BINDERS ***********)

definition cpx_ext (h) (G): relation3 lenv bind bind ≝
                            cext2 (cpx h G).

interpretation
   "uncounted context-sensitive parallel rt-transition (binder)"
   'PRedTy h G L I1 I2 = (cpx_ext h G L I1 I2).
