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

include "ground/relocation/trz_eq.ma".
include "ground/arith/int_plus_opp.ma".
include "ground/notation/functions/downspoonstar_2.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

definition trz_tls (z:int) (f:trz_map): trz_map ≝ mk_trz_map ….
[ @(λz0.f＠⧣❨z0+z❩-f＠⧣❨z❩)
| #z1 #z2 #Hz
  lapply (eq_inv_zplus_dx_bi … Hz) -Hz #Hz
  /3 width=3 by trz_injective, eq_inv_zplus_dx_bi/
]
defined.

interpretation
  "iterated tail (total relocation maps with integers)"
  'DownSpoonStar z f = (trz_tls z f).

(* Basic cnbstructions ******************************************************)

lemma trz_tls_unfold (f) (z) (z0):
      f＠⧣❨z0+z❩-f＠⧣❨z❩ = (⫰*[z]f)＠⧣❨z0❩.
// qed.

lemma trz_tls_eq_repl_fwd (z):
      compatible_2_fwd … trz_eq trz_eq (trz_tls z).
#z #f1 #f2 #Hf #z0
<trz_tls_unfold <trz_tls_unfold //
qed-.
