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

include "basic_2/substitution/gdrop.ma".

(* GLOBAL ENVIRONMENT SLICING ***********************************************)

(* Main properties **********************************************************)

theorem gdrop_mono: ∀G,G1,e. ⇩[e] G ≡ G1 → ∀G2. ⇩[e] G ≡ G2 → G1 = G2.
#G #G1 #e #H elim H -G -G1
[ #G #He #G2 #H
  >(gdrop_inv_gt … H He) -H -He //
| #G #He #G2 #H
  >(gdrop_inv_eq … H He) -H -He //
| #I #G #G1 #V #He #_ #IHG1 #G2 #H
  lapply (gdrop_inv_lt … H He) -H -He /2 width=1/
]
qed-.

lemma gdrop_dec: ∀G1,G2,e. Decidable (⇩[e] G1 ≡ G2).
#G1 #G2 #e
elim (gdrop_total e G1) #G #HG1
elim (genv_eq_dec G G2) #HG2
[ destruct /2 width=1/
| @or_intror #HG12
  lapply (gdrop_mono … HG1 … HG12) -HG1 -HG12 /2 width=1/
]
qed-.
