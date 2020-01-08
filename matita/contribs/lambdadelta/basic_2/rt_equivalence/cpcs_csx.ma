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

include "basic_2/rt_computation/cprre_csx.ma".
include "basic_2/rt_computation/cprre_cprre.ma".
include "basic_2/rt_equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Properties with strongly normalizing terms for unbound rt-transition *****)

(* Basic_1: was: cpcs_dec *)
lemma csx_cpcs_dec (h) (G) (L):
      ∀T1. ❪G,L❫ ⊢ ⬈*[h] 𝐒❪T1❫ → ∀T2. ❪G,L❫ ⊢ ⬈*[h] 𝐒❪T2❫ →
      Decidable … (❪G,L❫ ⊢ T1 ⬌*[h] T2).
#h #G #L #T1 #HT1 #T2 #HT2
elim (cprre_total_csx … HT1) -HT1 #U1 #HTU1
elim (cprre_total_csx … HT2) -HT2 #U2 #HTU2
elim (eq_term_dec U1 U2) [ #H destruct | #HnU12 ]
[ cases HTU1 -HTU1 #HTU1 #_
  cases HTU2 -HTU2 #HTU2 #_
  /3 width=3 by cprs_div, or_introl/
| @or_intror #H
  elim (cpcs_inv_cprs … H) -H #T0 #HT10 #HT20
  lapply (cprre_cprs_conf … HT10 … HTU1) -T1 #H1
  lapply (cprre_cprs_conf … HT20 … HTU2) -T2 #H2
  /3 width=6 by cprre_mono/
]
qed-.
