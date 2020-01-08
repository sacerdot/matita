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

include "basic_2/rt_transition/cpr.ma".

(* EXAMPLES *****************************************************************)

(* A reduction cycle in exactly three steps: the term Omega *****************)

definition Delta (s): term ≝ +ⓛ⋆s.ⓐ#0.#0.

definition Omega1 (s): term ≝ ⓐ(Delta s).(Delta s).

definition Omega2 (s): term ≝ +ⓓⓝ⋆s.(Delta s).ⓐ#0.#0.

definition Omega3 (s): term ≝ +ⓓⓝ⋆s.(Delta s).(Omega1 s).

(* Basic properties *********************************************************)

lemma Delta_lifts (f) (s): ⇧*[f] (Delta s) ≘ (Delta s).
/4 width=1 by lifts_lref, lifts_bind, lifts_flat/ qed.

(* Basic inversion properties ***********************************************)

lemma cpr_inv_Delta1_body_sn (h) (G) (L) (s):
                             ∀X. ❪G,L.ⓛ⋆s❫ ⊢ ⓐ#O.#O ➡[h] X → ⓐ#O.#O = X.
#h #G #L #s #X #H
lapply (cpm_inv_appl1 … H) -H * *
[ #W2 #T2 #HW2 #HT2 #H destruct
  elim (cpr_inv_zero1 … HW2) -HW2
  elim (cpr_inv_zero1 … HT2) -HT2
  [ #H1 #H2 destruct //
  | * #Y #X1 #X2 #_ #_ #H #_ destruct
  | #_ * #Y #X1 #X2 #_ #_ #H destruct
  | #_ * #Y #X1 #X2 #_ #_ #H destruct
  ]
| #p #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #H #_ destruct
| #p #V2 #V #W1 #W2 #T1 #T2 #_ #_ #_ #_ #H #_ destruct
]
qed-.

lemma cpr_inv_Delta_sn (h) (G) (L) (s):
                       ∀X. ❪G,L❫ ⊢ Delta s ➡[h] X → Delta s = X.
#h #G #L #s #X #H
elim (cpm_inv_abst1 … H) -H #X1 #X2 #H1 #H2 #H destruct
lapply (cpr_inv_sort1 … H1) -H1 #H destruct
<(cpr_inv_Delta1_body_sn … H2) -X2 //
qed-.

(* Main properties **********************************************************)

theorem cpr_Omega_12 (h) (G) (L) (s): ❪G,L❫ ⊢ Omega1 s ➡[h] Omega2 s.
/2 width=1 by cpm_beta/ qed.

theorem cpr_Omega_23 (h) (G) (L) (s): ❪G,L❫ ⊢ Omega2 s ➡[h] Omega3 s.
/5 width=3 by cpm_eps, cpm_appl, cpm_bind, cpm_delta, Delta_lifts/ qed.

theorem cpr_Omega_31 (h) (G) (L) (s): ❪G,L❫ ⊢ Omega3 s ➡[h] Omega1 s.
/4 width=3 by cpm_zeta, Delta_lifts, lifts_flat/ qed.

(* Main inversion properties ************************************************)

theorem cpr_inv_Omega1_sn (h) (G) (L) (s):
                          ∀X. ❪G,L❫ ⊢ Omega1 s ➡[h] X →
                          ∨∨ Omega1 s = X | Omega2 s = X.
#h #G #L #s #X #H elim (cpm_inv_appl1 … H) -H *
[ #W2 #T2 #HW2 #HT2 #H destruct
  <(cpr_inv_Delta_sn … HW2) -W2
  <(cpr_inv_Delta_sn … HT2) -T2
  /3 width=1 by refl, or_introl/
| #p #V2 #W1 #W2 #T1 #T2 #HV #HW #HT whd in ⊢ (??%?→?); #H1 #H2 destruct
  <(cpr_inv_Delta_sn … HV) -V2
  >(cpr_inv_sort1 … HW) -W2
  <(cpr_inv_Delta1_body_sn … HT) -T2 //
| #p #V2 #V #W1 #W2 #T1 #T2 #_ #_ #_ #_ whd in ⊢ (??%?→?); #H #_ destruct
]
qed-.

theorem cpr_Omega_21_false (h) (G) (L) (s): ❪G,L❫ ⊢ Omega2 s ➡[h] Omega1 s → ⊥.
#h #G #L #s #H elim (cpm_inv_bind1 … H) -H *
[ #W #T #_ #_ whd in ⊢ (??%?→?); #H destruct
| #X #H #_ #_ #_
  elim (lifts_inv_flat2 … H) -H #X1 #X2 #H1 #_ #_
  @(lifts_inv_lref2_uni_lt … H1) -H1 //
]
qed-.
