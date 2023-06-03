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

include "ground/relocation/trz_pnext.ma".
include "ground/relocation/trz_puni_le.ma".

(* POSITIVE NEXT FOR TOTAL RELOCATION MAPS WITH INTEGERS ********************)

(* Constuctions with zle ****************************************************)

lemma trz_pnext_gt (f) (z):
      (𝟎) < f＠⧣❨z❩ →
      ↑f＠⧣❨z❩ = (↑⁺f)＠⧣❨z❩.
/2 width=1 by trz_puni_gt/
qed.

lemma trz_pnext_le (f) (z):
      f＠⧣❨z❩ ≤ 𝟎 →
      f＠⧣❨z❩ = (↑⁺f)＠⧣❨z❩.
/2 width=1 by trz_puni_le/
qed.
