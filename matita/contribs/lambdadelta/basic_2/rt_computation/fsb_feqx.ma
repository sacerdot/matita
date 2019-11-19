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

include "basic_2/rt_transition/fpb_feqx.ma".
include "basic_2/rt_computation/fsb.ma".

(* STRONGLY NORMALIZING CLOSURES FOR PARALLEL RST-TRANSITION ****************)

(* Properties with sort-irrelevant equivalence for closures *****************)

lemma fsb_feqx_trans: ∀h,G1,L1,T1. ≥[h] 𝐒⦃G1,L1,T1⦄ →
                      ∀G2,L2,T2. ⦃G1,L1,T1⦄ ≛ ⦃G2,L2,T2⦄ → ≥[h] 𝐒⦃G2,L2,T2⦄.
#h #G1 #L1 #T1 #H @(fsb_ind_alt … H) -G1 -L1 -T1
#G1 #L1 #T1 #_ #IH #G2 #L2 #T2 #H12
@fsb_intro #G #L #T #H2
elim (feqx_fpb_trans … H12 … H2) -G2 -L2 -T2
/2 width=5 by/
qed-.
