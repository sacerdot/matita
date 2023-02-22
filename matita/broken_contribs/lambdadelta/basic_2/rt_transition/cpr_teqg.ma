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

include "static_2/relocation/lifts_teqg.ma".
include "basic_2/rt_transition/cpr_drops_basic.ma".

(* CONTEXT-SENSITIVE PARALLEL R-TRANSITION FOR TERMS ************************)

(* Properties with context-free generic equivalence *************************)

lemma cpr_abbr_pos_tneqx (S) (h) (G) (L) (V) (T1):
      symmetric … S → (∀s1,s2. Decidable (S s1 s2)) →
      ∃∃T2. ❨G,L❩ ⊢ +ⓓV.T1 ➡[h,0] T2 & (+ⓓV.T1 ≛[S] T2 → ⊥).
#S #h #G #L #V #U1 #H1S #H2S
elim (cpr_subst h G (L.ⓓV) U1 … 0) [|*: /2 width=4 by drops_refl/ ] #U2 #T2 #HU12 #HTU2
elim (teqg_dec … H2S U1 U2) [ -HU12 #HU12 | -HTU2 #HnU12 ]
[ elim (teqg_inv_lifts_dx … HU12 … HTU2) -U2 // #T1 #HTU1 #_ -T2
  /3 width=9 by cpm_zeta, teqg_lifts_inv_pair_sn, ex2_intro/
| @(ex2_intro … (+ⓓV.U2)) [ /2 width=1 by cpm_bind/ ] -HU12 #H
  elim (teqg_inv_pair … H) -H #_ #_ /2 width=1 by/
]
qed-.
