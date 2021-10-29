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

include "basic_2/rt_computation/fpbs_fpbs.ma".
include "basic_2/rt_computation/fpbg.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Advanced forward lemmas **************************************************)

lemma fpbg_fwd_fpbs (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ > ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H
elim (fpbg_inv_gen … H) -H
/4 width=9 by fpbs_trans, fpbs_strap2, fpbc_fwd_fpb/
qed-.

(* Advanced properties ******************************************************)

lemma fpbs_fpbg_trans (G) (L) (T):
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≥ ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ > ❨G2,L2,T2❩ → ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
#G #L #T #G1 #L1 #T1 #H1 #G2 #L2 #T2 #H2
elim (fpbg_inv_gen … H2) -H2
/3 width=13 by fpbg_intro, fpbs_trans/
qed-.

(* Note: this is used in the closure proof *)
lemma fpbg_fpbs_trans (G) (L) (T):
      ∀G1,L1,T1. ❨G1,L1,T1❩ > ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ≥ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ > ❨G2,L2,T2❩.
#G #L #T #G1 #L1 #T1 #H1 #G2 #L2 #T2 #H2
elim (fpbg_inv_gen … H1) -H1
/3 width=13 by fpbg_intro, fpbs_trans/
qed-.
