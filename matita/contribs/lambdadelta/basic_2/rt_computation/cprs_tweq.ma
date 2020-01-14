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

include "static_2/syntax/tweq_tweq.ma".
include "static_2/relocation/lifts_tweq.ma".
include "basic_2/rt_transition/cpr_drops_basic.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Properties with sort-irrelevant whd equivalence on terms *****************)

lemma cprs_abbr_pos_twneq (h) (G) (L) (V) (T1):
      ∃∃T2. ❪G,L❫ ⊢ +ⓓV.T1 ➡*[h,0] T2 & (+ⓓV.T1 ≅ T2 → ⊥).
#h #G #L #V #U1
elim (cpr_subst h G (L.ⓓV) U1 … 0) [|*: /2 width=4 by drops_refl/ ] #U2 #T2 #HU12 #HTU2
elim (tweq_dec U1 U2) [ #HpU12 | -HTU2 #HnU12 ]
[ @(ex2_intro … T2) (**) (* full auto not tried *)
  [ /3 width=6 by cpms_zeta, cpms_step_sn, cpm_bind/
  | /4 width=6 by tweq_inv_abbr_pos_x_lifts_y_y, tweq_canc_sn, tweq_abbr_pos/
  ]
| /4 width=3 by cpm_cpms, cpm_bind, tweq_inv_abbr_pos_bi, ex2_intro/
]
qed-.
