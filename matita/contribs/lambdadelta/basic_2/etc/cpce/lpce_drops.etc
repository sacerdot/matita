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

include "static_2/relocation/drops_lex.ma".
include "basic_2/rt_conversion/lpce.ma".

(* PARALLEL ETA-CONVERSION FOR FULL LOCAL ENVIRONMENTS **********************)

(* Inversion lemmas with generic slicing for local environments *************)

lemma lpce_drops_conf (h) (G): dropable_sn (cpce h G).
/2 width=3 by lex_dropable_sn/ qed-.

lemma lpce_drops_trans (h) (G): dropable_dx (cpce h G).
/2 width=3 by lex_dropable_dx/ qed-.
