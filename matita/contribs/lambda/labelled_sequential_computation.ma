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

include "pointer_sequence.ma".
include "labelled_sequential_reduction.ma".

(* LABELLED SEQUENTIAL COMPUTATION (MULTISTEP) ******************************)

definition lsreds: pseq → relation term ≝ lstar … lsred.

interpretation "labelled sequential computation"
   'SeqRedStar M s N = (lsreds s M N).

notation "hvbox( M break ⇀* [ term 46 s ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRedStar $M $s $N }.

lemma lsred_lsreds: ∀p,M1,M2. M1 ⇀[p] M2 → M1 ⇀*[p::◊] M2.
/2 width=1/
qed.

lemma lsreds_inv_nil: ∀s,M1,M2. M1 ⇀*[s] M2 → ◊ = s → M1 = M2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma lsreds_inv_cons: ∀s,M1,M2. M1 ⇀*[s] M2 → ∀q,r. q::r = s →
                       ∃∃M. M1 ⇀[q] M & M ⇀*[r] M2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma lsreds_inv_lsred: ∀p,M1,M2. M1 ⇀*[p::◊] M2 → M1 ⇀[p] M2.
/2 width=1 by lstar_inv_step/
qed-.

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

theorem lsreds_trans: ∀s1,M1,M. M1 ⇀*[s1] M →
                      ∀s2,M2. M ⇀*[s2] M2 → M1 ⇀*[s1@s2] M2.
/2 width=3 by lstar_trans/
qed-.

(* Note: "|s|" should be unparetesized *)
lemma lsreds_fwd_mult: ∀s,M1,M2. M1 ⇀*[s] M2 → #{M2} ≤ #{M1} ^ (2 ^ (|s|)).
#s #M1 #M2 #H @(lstar_ind_l ????????? H) -s -M1 normalize //
#p #s #M1 #M #HM1 #_ #IHM2
lapply (lsred_fwd_mult … HM1) -p #HM1
@(transitive_le … IHM2) -M2
/3 width=1 by le_exp1, lt_O_exp, lt_to_le/ (**) (* auto: slow without trace *)
qed-.
