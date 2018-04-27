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

include "basic_2/static/gcp.ma".
include "basic_2/rt_transition/cnx_drops.ma".
include "basic_2/rt_computation/csx_drops.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Main properties with generic computation properties **********************)

theorem csx_gcp: ∀h,o. gcp (cpx h) (tdeq h o) (csx h o).
#h #o @mk_gcp
[ normalize /3 width=13 by cnx_lifts/
| #G #L elim (deg_total h o 0) /3 width=8 by cnx_sort_iter, ex_intro/
| /2 width=8 by csx_lifts/
| /2 width=3 by csx_fwd_flat_dx/
]
qed.
