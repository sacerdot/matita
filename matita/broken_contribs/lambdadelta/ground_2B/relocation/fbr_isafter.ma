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

include "ground/subsets/subset.ma".
include "ground/relocation/fb/fbr_after_eq.ma".
include "ground_2B/notation/functions/circledring_2.ma".

(* COMPOSITION CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

definition fbr_isafter (g) (f): 𝒫❨𝔽𝔹❩ ≝
           {h | h ≐ g•f}.

interpretation
  "composition class (finite relocation maps with booleans)"
  'CircledRing g f = (fbr_isafter g f).

(* Basic constructions ******************************************************)

lemma fbr_isafter_id_sn (f1):
      f1 ϵ 𝐢 ⊚ f1.
//
qed.

lemma fbr_isafter_id_dx (f2):
      f2 ϵ f2 ⊚ 𝐢.
//
qed.

lemma fbr_isafter_push_bi (f1) (f2) (f):
      f ϵ f2 ⊚ f1 → ⫯f ϵ ⫯f2 ⊚ ⫯f1.
/2 width=1 by fbr_eq_rcons_bi/
qed.

lemma fbr_isafter_push_next (f1) (f2) (f):
      f ϵ f2 ⊚ f1 → ↑f ϵ ⫯f2 ⊚ ↑f1.
/2 width=1 by fbr_eq_rcons_bi/
qed.

lemma fbr_isafter_next_sn (f1) (f2) (f):
      f ϵ f2 ⊚ f1 → ↑f ϵ ↑f2 ⊚ f1.
/2 width=1 by fbr_isafter_push_next/
qed.
