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

include "terms/pointer_list.ma".
include "terms/parallel_computation.ma".

(* LABELED SEQUENTIAL COMPUTATION (MULTISTEP) *******************************)

definition lsreds: ptrl → relation term ≝ lstar … lsred.

interpretation "labelled sequential computation"
   'SeqRedStar M s N = (lsreds s M N).

notation "hvbox( M break ↦* [ term 46 s ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRedStar $M $s $N }.

lemma lsreds_refl: reflexive … (lsreds (◊)).
//
qed.

lemma lsreds_step_sn: ∀p,M1,M. M1 ↦[p] M → ∀s,M2. M ↦*[s] M2 → M1 ↦*[p::s] M2.
/2 width=3/
qed-.

lemma lsreds_step_dx: ∀s,M1,M. M1 ↦*[s] M → ∀p,M2. M ↦[p] M2 → M1 ↦*[s@p::◊] M2.
/2 width=3/
qed-.

lemma lsreds_step_rc: ∀p,M1,M2. M1 ↦[p] M2 → M1 ↦*[p::◊] M2.
/2 width=1/
qed.

lemma lsreds_inv_nil: ∀s,M1,M2. M1 ↦*[s] M2 → ◊ = s → M1 = M2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma lsreds_inv_cons: ∀s,M1,M2. M1 ↦*[s] M2 → ∀q,r. q::r = s →
                       ∃∃M. M1 ↦[q] M & M ↦*[r] M2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma lsreds_inv_step_rc: ∀p,M1,M2. M1 ↦*[p::◊] M2 → M1 ↦[p] M2.
/2 width=1 by lstar_inv_step/
qed-.

lemma lsreds_inv_pos: ∀s,M1,M2. M1 ↦*[s] M2 → 0 < |s| →
                      ∃∃p,r,M. p::r = s & M1 ↦[p] M & M ↦*[r] M2.
/2 width=1 by lstar_inv_pos/
qed-.

lemma lsred_compatible_rc: ho_compatible_rc lsreds.
/3 width=1/
qed.

lemma lsreds_compatible_sn: ho_compatible_sn lsreds.
/3 width=1/
qed.

lemma lsreds_compatible_dx: ho_compatible_dx lsreds.
/3 width=1/
qed.

lemma lsreds_lift: ∀s. liftable (lsreds s).
/2 width=1/
qed.

lemma lsreds_inv_lift: ∀s. deliftable_sn (lsreds s).
/3 width=3 by lstar_deliftable_sn, lsred_inv_lift/
qed-.

lemma lsreds_dsubst: ∀s. dsubstable_dx (lsreds s).
/2 width=1/
qed.

theorem lsreds_mono: ∀s. singlevalued … (lsreds s).
/3 width=7 by lstar_singlevalued, lsred_mono/
qed-.

theorem lsreds_trans: ltransitive … lsreds.
/2 width=3 by lstar_ltransitive/
qed-.

lemma lsreds_compatible_appl: ∀r,B1,B2. B1 ↦*[r] B2 → ∀s,A1,A2. A1 ↦*[s] A2 →
                              @B1.A1 ↦*[(sn:::r)@dx:::s] @B2.A2.
#r #B1 #B2 #HB12 #s #A1 #A2 #HA12
@(lsreds_trans … (@B2.A1)) /2 width=1/
qed.

lemma lsreds_compatible_beta: ∀r,B1,B2. B1 ↦*[r] B2 → ∀s,A1,A2. A1 ↦*[s] A2 →
                              @B1.𝛌.A1 ↦*[(sn:::r)@(dx:::rc:::s)@◊::◊] [↙B2] A2.
#r #B1 #B2 #HB12 #s #A1 #A2 #HA12
@(lsreds_trans … (@B2.𝛌.A1)) /2 width=1/ -r -B1
@(lsreds_step_dx … (@B2.𝛌.A2)) // /3 width=1/
qed.

(* Note: "|s|" should be unparetesized *)
lemma lsreds_fwd_mult: ∀s,M1,M2. M1 ↦*[s] M2 → ♯{M2} ≤ ♯{M1} ^ (2 ^ (|s|)).
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 normalize //
#p #s #M1 #M #HM1 #_ #IHM2
lapply (lsred_fwd_mult … HM1) -p #HM1
@(transitive_le … IHM2) -M2
/3 width=1 by le_exp1, lt_O_exp, lt_to_le/ (**) (* auto: slow without trace *)
qed-.

theorem lsreds_preds: ∀s,M1,M2. M1 ↦*[s] M2 → M1 ⤇* M2.
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 //
#a #s #M1 #M #HM1 #_ #IHM2
@(preds_step_sn … IHM2) -M2 /2 width=2/
qed.

lemma pred_lsreds: ∀M1,M2. M1 ⤇ M2 → ∃r. M1 ↦*[r] M2.
#M1 #M2 #H elim H -M1 -M2 /2 width=2/
[ #A1 #A2 #_ * /3 width=2/
| #B1 #B2 #A1 #A2 #_ #_ * #r #HB12 * /3 width=2/
| #B1 #B2 #A1 #A2 #_ #_ * #r #HB12 * /3 width=2/
qed-.

theorem preds_lsreds: ∀M1,M2. M1 ⤇* M2 → ∃r. M1 ↦*[r] M2.
#M1 #M2 #H elim H -M2 /2 width=2/
#M #M2 #_ #HM2 * #r #HM1
elim (pred_lsreds … HM2) -HM2 #s #HM2
lapply (lsreds_trans … HM1 … HM2) -M /2 width=2/
qed-.

theorem lsreds_conf: ∀s1,M0,M1. M0 ↦*[s1] M1 → ∀s2,M2. M0 ↦*[s2] M2 →
                     ∃∃r1,r2,M. M1 ↦*[r1] M & M2 ↦*[r2] M.
#s1 #M0 #M1 #HM01 #s2 #M2 #HM02
lapply (lsreds_preds … HM01) -s1 #HM01
lapply (lsreds_preds … HM02) -s2 #HM02
elim (preds_conf … HM01 … HM02) -M0 #M #HM1 #HM2
elim (preds_lsreds … HM1) -HM1
elim (preds_lsreds … HM2) -HM2 /2 width=5/
qed-.
