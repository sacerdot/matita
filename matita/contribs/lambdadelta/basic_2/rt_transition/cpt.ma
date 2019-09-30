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

include "ground_2/steps/rtc_ist_shift.ma".
include "ground_2/steps/rtc_ist_plus.ma".
include "ground_2/steps/rtc_ist_max.ma".
include "basic_2/notation/relations/pty_6.ma".
include "basic_2/rt_transition/cpg.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

definition cpt (h) (G) (L) (n): relation2 term term ≝
           λT1,T2. ∃∃c. 𝐓⦃n,c⦄ & ⦃G,L⦄ ⊢ T1 ⬈[eq …,c,h] T2.

interpretation
  "t-bound context-sensitive parallel t-transition (term)"
  'PTy h n G L T1 T2 = (cpt h G L n T1 T2).

(* Basic properties *********************************************************)

lemma cpt_ess (h) (G) (L):
      ∀s. ⦃G,L⦄ ⊢ ⋆s ⬆[h,1] ⋆(⫯[h]s).
/2 width=3 by cpg_ess, ex2_intro/ qed.

lemma cpt_delta (h) (n) (G) (K):
      ∀V1,V2. ⦃G,K⦄ ⊢ V1 ⬆[h,n] V2 →
      ∀W2. ⇧*[1] V2 ≘ W2 → ⦃G,K.ⓓV1⦄ ⊢ #0 ⬆[h,n] W2.
#h #n #G #K #V1 #V2 *
/3 width=5 by cpg_delta, ex2_intro/
qed.

lemma cpt_ell (h) (n) (G) (K):
      ∀V1,V2. ⦃G,K⦄ ⊢ V1 ⬆[h,n] V2 →
      ∀W2. ⇧*[1] V2 ≘ W2 → ⦃G,K.ⓛV1⦄ ⊢ #0 ⬆[h,↑n] W2.
#h #n #G #K #V1 #V2 *
/3 width=5 by cpg_ell, ex2_intro, ist_succ/
qed.

lemma cpt_lref (h) (n) (G) (K):
      ∀T,i. ⦃G,K⦄ ⊢ #i ⬆[h,n] T → ∀U. ⇧*[1] T ≘ U →
      ∀I. ⦃G,K.ⓘ{I}⦄ ⊢ #↑i ⬆[h,n] U.
#h #n #G #K #T #i *
/3 width=5 by cpg_lref, ex2_intro/
qed.

lemma cpt_bind (h) (n) (G) (L):
      ∀V1,V2. ⦃G,L⦄ ⊢ V1 ⬆[h,0] V2 → ∀I,T1,T2. ⦃G,L.ⓑ{I}V1⦄ ⊢ T1 ⬆[h,n] T2 →
      ∀p. ⦃G,L⦄ ⊢ ⓑ{p,I}V1.T1 ⬆[h,n] ⓑ{p,I}V2.T2.
#h #n #G #L #V1 #V2 * #cV #HcV #HV12 #I #T1 #T2 *
/3 width=5 by cpg_bind, ist_max_O1, ex2_intro/
qed.

lemma cpt_appl (h) (n) (G) (L):
      ∀V1,V2. ⦃G,L⦄ ⊢ V1 ⬆[h,0] V2 →
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 → ⦃G,L⦄ ⊢ ⓐV1.T1 ⬆[h,n] ⓐV2.T2.
#h #n #G #L #V1 #V2 * #cV #HcV #HV12 #T1 #T2 *
/3 width=5 by ist_max_O1, cpg_appl, ex2_intro/
qed.

lemma cpt_cast (h) (n) (G) (L):
      ∀U1,U2. ⦃G,L⦄ ⊢ U1 ⬆[h,n] U2 →
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 → ⦃G,L⦄ ⊢ ⓝU1.T1 ⬆[h,n] ⓝU2.T2.
#h #n #G #L #U1 #U2 * #cU #HcU #HU12 #T1 #T2 *
/3 width=6 by cpg_cast, ex2_intro/
qed.

lemma cpt_ee (h) (n) (G) (L):
      ∀U1,U2. ⦃G,L⦄ ⊢ U1 ⬆[h,n] U2 → ∀T. ⦃G,L⦄ ⊢ ⓝU1.T ⬆[h,↑n] U2.
#h #n #G #L #V1 #V2 *
/3 width=3 by cpg_ee, ist_succ, ex2_intro/
qed.

(* Basic properties *********************************************************)

lemma cpt_refl (h) (G) (L): reflexive … (cpt h G L 0).
/3 width=3 by cpg_refl, ex2_intro/ qed.

(* Advanced properties ******************************************************)

lemma cpt_sort (h) (G) (L):
      ∀n. n ≤ 1 → ∀s. ⦃G,L⦄ ⊢ ⋆s ⬆[h,n] ⋆((next h)^n s).
#h #G #L * //
#n #H #s <(le_n_O_to_eq n) /2 width=1 by le_S_S_to_le/
qed.
