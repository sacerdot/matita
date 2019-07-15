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

include "static_2/static/gcp.ma".
include "basic_2/rt_transition/cnx_drops.ma".
include "basic_2/rt_computation/csx_drops.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Main properties with generic computation properties **********************)

theorem csx_gcp: ∀h. gcp (cpx h) tdeq (csx h).
#h @mk_gcp
[ normalize /3 width=13 by cnx_lifts/
| /2 width=4 by cnx_sort/
| /2 width=8 by csx_lifts/
| /2 width=3 by csx_fwd_flat_dx/
]
qed.
