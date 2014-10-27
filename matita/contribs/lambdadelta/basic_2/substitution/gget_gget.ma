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

include "basic_2/substitution/gget.ma".

(* GLOBAL ENVIRONMENT READING ***********************************************)

(* Main properties **********************************************************)

theorem gget_mono: ∀G,G1,m. ⬇[m] G ≡ G1 → ∀G2. ⬇[m] G ≡ G2 → G1 = G2.
#G #G1 #m #H elim H -G -G1
[ #G #Hm #G2 #H
  >(gget_inv_gt … H Hm) -H -Hm //
| #G #Hm #G2 #H
  >(gget_inv_eq … H Hm) -H -Hm //
| #I #G #G1 #V #Hm #_ #IHG1 #G2 #H
  lapply (gget_inv_lt … H Hm) -H -Hm /2 width=1 by/
]
qed-.

lemma gget_dec: ∀G1,G2,m. Decidable (⬇[m] G1 ≡ G2).
#G1 #G2 #m
elim (gget_total m G1) #G #HG1
elim (eq_genv_dec G G2) #HG2
[ destruct /2 width=1 by or_introl/
| @or_intror #HG12
  lapply (gget_mono … HG1 … HG12) -HG1 -HG12 /2 width=1 by/
]
qed-.
