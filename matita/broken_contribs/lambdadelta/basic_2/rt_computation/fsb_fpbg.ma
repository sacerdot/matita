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

include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/fpbg_feqg.ma".
include "basic_2/rt_computation/fsb_feqg.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Properties with parallel rst-computation for closures ********************)

lemma fsb_fpbs_trans:
      ∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ → ≥𝐒 ❨G2,L2,T2❩.
#G1 #L1 #T1 #H @(fsb_ind … H) -G1 -L1 -T1
#G1 #L1 #T1 #H1 #IH #G2 #L2 #T2 #H12
elim (fpbs_inv_fpbg … H12) -H12
[ -IH /2 width=9 by fsb_feqg_trans/
| -H1 #H elim (fpbg_inv_fpbc_fpbs … H)
  /2 width=5 by/
]
qed-.

(* Properties with parallel rst-transition for closures *********************)

lemma fsb_fpb_trans:
      ∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩ → ≥𝐒 ❨G2,L2,T2❩.
/3 width=5 by fsb_fpbs_trans, fpb_fpbs/ qed-.

(* Properties with proper parallel rst-computation for closures *************)

lemma fsb_intro_fpbg:
      ∀G1,L1,T1.
      (∀G2,L2,T2. ❨G1,L1,T1❩ > ❨G2,L2,T2❩ → ≥𝐒 ❨G2,L2,T2❩) →
      ≥𝐒 ❨G1,L1,T1❩.
/4 width=1 by fsb_intro, fpbc_fpbg/ qed.

(* Eliminators with proper parallel rst-computation for closures ************)

lemma fsb_ind_fpbg_fpbs (Q:relation3 …):
      (∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
        (∀G2,L2,T2. ❨G1,L1,T1❩ > ❨G2,L2,T2❩ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
      ∀G2,L2,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ → Q G2 L2 T2.
#Q #IH1 #G1 #L1 #T1 #H @(fsb_ind … H) -G1 -L1 -T1
#G1 #L1 #T1 #H1 #IH #G2 #L2 #T2 #H12
@IH1 -IH1
[ -IH /2 width=5 by fsb_fpbs_trans/
| -H1 #G0 #L0 #T0 #H10
  lapply (fpbs_fpbg_trans … H12 … H10) -G2 -L2 -T2 #H
  elim (fpbg_inv_fpbc_fpbs … H) -H #G #L #T #H1 #H0
  /2 width=5 by/
]
qed-.

lemma fsb_ind_fpbg (Q:relation3 …):
      (∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →
        (∀G2,L2,T2. ❨G1,L1,T1❩ > ❨G2,L2,T2❩ → Q G2 L2 T2) →
        Q G1 L1 T1
      ) →
      ∀G1,L1,T1. ≥𝐒 ❨G1,L1,T1❩ →  Q G1 L1 T1.
#Q #IH #G1 #L1 #T1 #H @(fsb_ind_fpbg_fpbs … H) -H
/3 width=1 by/
qed-.

(* Inversion lemmas with proper parallel rst-computation for closures *******)

lemma fsb_fpbg_refl_false (G) (L) (T):
      ≥𝐒 ❨G,L,T❩ → ❨G,L,T❩ > ❨G,L,T❩ → ⊥.
#G #L #T #H
@(fsb_ind_fpbg … H) -G -L -T #G1 #L1 #T1 #_ #IH #H
/2 width=5 by/
qed-.
