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

include "ground/relocation/tz/tzr_map.ma".
include "ground/arith/int_plus_opp.ma".
include "ground/notation/functions/downspoonstar_2.ma".

(* ITERATED TAIL FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

definition tzr_tls (z:int) (f:tzr_map): tzr_map ≝ mk_tzr_map ….
[ @(λz0.f＠⧣❨z0+z❩-f＠⧣❨z❩)
| #z1 #z2 #Hz
  lapply (eq_inv_zplus_dx_bi … Hz) -Hz #Hz
  /3 width=3 by tzr_injective, eq_inv_zplus_dx_bi/
]
defined.

interpretation
  "iterated tail (total relocation maps with integers)"
  'DownSpoonStar z f = (tzr_tls z f).

(* Basic cnnstructions ******************************************************)

lemma tzr_tls_dapp (f) (z) (z0):
      f＠⧣❨z0+z❩-f＠⧣❨z❩ = (⫰*[z]f)＠⧣❨z0❩.
// qed.

lemma tzr_dapp_plus (f) (z1) (z2):
      (⫰*[z2]f)＠⧣❨z1❩+f＠⧣❨z2❩ = f＠⧣❨z1+z2❩.
#f #z1 #z2
<tzr_tls_dapp <zminus_plus_simpl //
qed.

lemma tzr_tls_eq_repl (z):
      compatible_2_fwd … tzr_eq tzr_eq (λf.⫰*[z]f).
#z #f1 #f2 #Hf #z0
<tzr_tls_dapp <tzr_tls_dapp //
qed-.

(* Main constructions *******************************************************)

theorem tzr_tls_plus (f) (z1) (z2):
        (⫰*[z1]⫰*[z2]f) ≐ ⫰*[z1+z2]f.
#f #z1 #z2 #z0
<tzr_tls_dapp <tzr_tls_dapp <tzr_tls_dapp
>zplus_opp_bi <zplus_assoc //
qed.
