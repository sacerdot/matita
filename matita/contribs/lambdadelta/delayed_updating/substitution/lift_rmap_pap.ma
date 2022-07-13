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

include "delayed_updating/substitution/lift_rmap.ma".
include "ground/relocation/tr_pap_tls.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Constructions with tr_pap ************************************************)

lemma lift_rmap_pap_d_dx (f) (p) (k) (h):
      ↑[p]f＠⧣❨h+k❩ = ↑[p◖𝗱k]f＠⧣❨h❩+↑[p]f＠⧣❨k❩.
// qed.
