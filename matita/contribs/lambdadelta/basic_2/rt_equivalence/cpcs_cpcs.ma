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

include "basic_2/rt_equivalence/cpcs_lprs.ma".

(* CONTEXT-SENSITIVE PARALLEL R-EQUIVALENCE FOR TERMS ***********************)

(* Main properties **********************************************************)

(* Basic_1: was pc3_t *)
theorem cpcs_trans (h) (G) (L): Transitive … (cpcs h G L).
#h #G #L #T1 #T #HT1 #T2 @(trans_TC … HT1)
qed-.

theorem cpcs_canc_sn (h) (G) (L): left_cancellable … (cpcs h G L).
/3 width=3 by cpcs_trans, cpcs_sym/ qed-.

theorem cpcs_canc_dx (h) (G) (L): right_cancellable … (cpcs h G L).
/3 width=3 by cpcs_trans, cpcs_sym/ qed-.

(* Advanced properties ******************************************************)

lemma cpcs_bind1 (h) (G) (L): ∀V1,V2. ⦃G, L⦄ ⊢ V1 ⬌*[h] V2 →
                              ∀I,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ⬌*[h] T2 →
                              ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬌*[h] ⓑ{p,I}V2.T2.
/3 width=3 by cpcs_trans, cpcs_bind_sn, cpcs_bind_dx/ qed.

lemma cpcs_bind2 (h) (G) (L): ∀V1,V2. ⦃G, L⦄ ⊢ V1 ⬌*[h] V2 →
                              ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬌*[h] T2 →
                              ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬌*[h] ⓑ{p,I}V2.T2.
/3 width=3 by cpcs_trans, cpcs_bind_sn, cpcs_bind_dx/ qed.

(* Advanced properties with r-transition for full local environments ********)

(* Basic_1: was: pc3_wcpr0 *)
lemma lpr_cpcs_conf (h) (G): ∀L1,L2. ⦃G, L1⦄ ⊢ ➡[h] L2 →
                             ∀T1,T2. ⦃G, L1⦄ ⊢ T1 ⬌*[h] T2 → ⦃G, L2⦄ ⊢ T1 ⬌*[h] T2.
#h #G #L1 #L2 #HL12 #T1 #T2 #H elim (cpcs_inv_cprs … H) -H
/3 width=5 by cpcs_canc_dx, lpr_cprs_conf/
qed-.
