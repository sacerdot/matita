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

include "basic_2/rt_transition/fpb_fqup.ma".
include "basic_2/rt_computation/fpbs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Advanced eliminators *****************************************************)

lemma fpbs_ind:
      ∀G1,L1,T1. ∀Q:relation3 genv lenv term. Q G1 L1 T1 →
      (∀G,G2,L,L2,T,T2. ❨G1,L1,T1❩ ≥ ❨G,L,T❩ → ❨G,L,T❩ ≽ ❨G2,L2,T2❩ → Q G L T → Q G2 L2 T2) →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ → Q G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma fpbs_ind_dx:
      ∀G2,L2,T2. ∀Q:relation3 genv lenv term. Q G2 L2 T2 →
      (∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≽ ❨G,L,T❩ → ❨G,L,T❩ ≥ ❨G2,L2,T2❩ → Q G L T → Q G1 L1 T1) →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ → Q G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Advanced properties ******************************************************)

lemma fpbs_refl:
      tri_reflexive … fpbs.
/2 width=1 by tri_inj/ qed.

(* Properties with plus-iterated structural successor for closures **********)

lemma fqup_fpbs:
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ⬂+ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/4 width=5 by fqu_fquq, fquq_fpb, tri_step/
qed.

lemma fpbs_fqup_trans:
      ∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≥ ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ⬂+ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fpbs_strap1, fqu_fpb/
qed-.

lemma fqup_fpbs_trans:
      ∀G,G2,L,L2,T,T2. ❨G,L,T❩ ≥ ❨G2,L2,T2❩ →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ⬂+ ❨G,L,T❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G #G2 #L #L2 #T #T2 #H1 #G1 #L1 #T1 #H @(fqup_ind_dx … H) -G1 -L1 -T1
/3 width=9 by fpbs_strap2, fqu_fpb/
qed-.