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

include "static_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Main inversion lemmas ****************************************************)

theorem aaa_mono: ∀G,L,T,A1. ❨G,L❩ ⊢ T ⁝ A1 → ∀A2. ❨G,L❩ ⊢ T ⁝ A2 → A1 = A2.
#G #L #T #A1 #H elim H -G -L -T -A1
[ #G #L #s #A2 #H >(aaa_inv_sort … H) -H //
| #I1 #G #L #V1 #B #_ #IH #A2 #H
  elim (aaa_inv_zero … H) -H #I2 #K2 #V2 #H #HA2 destruct /2 width=1 by/
| #I1 #G #L #B #i #_ #IH #A2 #H
  elim (aaa_inv_lref … H) -H #I2 #K2 #H #HA2 destruct /2 width=1 by/
| #p #G #L #V #T #B1 #A1 #_ #_ #_ #IH #A2 #H
  elim (aaa_inv_abbr … H) -H /2 width=1 by/
| #p #G #L #V1 #T1 #B1 #A1 #_ #_ #IHB1 #IHA1 #X #H
  elim (aaa_inv_abst … H) -H #B2 #A2 #HB2 #HA2 #H destruct /3 width=1 by eq_f2/
| #G #L #V1 #T1 #B1 #A1 #_ #_ #_ #IHA1 #A2 #H
  elim (aaa_inv_appl … H) -H #B2 #_ #HA2
  lapply (IHA1 … HA2) -L #H destruct //
| #G #L #V #T #A1 #_ #_ #_ #IHA1 #A2 #H
  elim (aaa_inv_cast … H) -H /2 width=1 by/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma aaa_aaa_inv_appl (G) (L) (V) (T) (B) (X):
      ∀A. ❨G,L❩ ⊢ ⓐV.T ⁝ A → ❨G,L❩ ⊢ V ⁝ B → ❨G,L❩⊢ T ⁝ X → ②B.A = X.
#G #L #V #T #B #X #A #H #H1V #H1T
elim (aaa_inv_appl … H) -H #B0 #H2V #H2T
lapply (aaa_mono … H2V … H1V) -V #H destruct
lapply (aaa_mono … H2T … H1T) -G -L -T //
qed-.

lemma aaa_aaa_inv_cast (G) (L) (U) (T) (B) (A):
      ∀X. ❨G,L❩ ⊢ ⓝU.T ⁝ X → ❨G,L❩ ⊢ U ⁝ B → ❨G,L❩⊢ T ⁝ A → ∧∧ B = X & A = X.
#G #L #U #T #B #A #X #H #H1U #H1T
elim (aaa_inv_cast … H) -H #H2U #H2T
lapply (aaa_mono … H1U … H2U) -U #HB
lapply (aaa_mono … H1T … H2T) -G -L -T #HA
/2 width=1 by conj/
qed-.
