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

include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_transition/lpx_aaa.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with atomic arity assignment for terms ************************)

(* Basic_2A1: includes: cpr_aaa_conf *)
lemma cpm_aaa_conf (n) (h): ∀G,L. Conf3 … (aaa G L) (cpm h G L n).
/3 width=5 by cpx_aaa_conf, cpm_fwd_cpx/ qed-.

(* Note: one of these U is the inferred type of T *)
lemma aaa_cpm_SO (h) (G) (L) (A):
      ∀T. ⦃G,L⦄ ⊢ T ⁝ A → ∃U. ⦃G,L⦄ ⊢ T ➡[1,h] U.
#h #G #L #A #T #H elim H -G -L -T -A
[ /3 width=2 by ex_intro/
| * #G #L #V #B #_ * #V0 #HV0
  [ elim (lifts_total V0 (𝐔❴1❵)) #W0 #HVW0
    /3 width=4 by cpm_delta, ex_intro/
  | elim (lifts_total V (𝐔❴1❵)) #W #HVW -V0
    /3 width=4 by cpm_ell, ex_intro/
  ]
| #I #G #L #A #i #_ * #T0 #HT0
  elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
  /3 width=4 by cpm_lref, ex_intro/
| #p #G #L #V #T #B #A #_ #_ #_ * #T0 #HT0
  /3 width=2 by cpm_bind, ex_intro/
| #p #G #L #V #T #B #A #_ #_ #_  * #T0 #HT0
  /3 width=2 by cpm_bind, ex_intro/
| #G #L #V #T #B #A #_ #_ #_ * #T0 #HT0
  /3 width=2 by cpm_appl, ex_intro/
| #G #L #U #T #A #_ #_ * #U0 #HU0 * #T0 #HT0
  /3 width=2 by cpm_cast, ex_intro/
]
qed-.
