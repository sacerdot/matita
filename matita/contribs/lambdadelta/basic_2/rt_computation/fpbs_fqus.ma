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

include "static_2/s_computation/fqus.ma".
include "basic_2/rt_computation/fpbs_fqup.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with star-iterated structural successor for closures **********)

lemma fqus_fpbs:
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ⬂* ❨G2,L2,T2❩ →
      ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2
/3 width=5 by fquq_fpb, fpbs_strap1/
qed.

lemma fpbs_fqus_trans:
      ∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≥ ❨G,L,T❩ →
      ∀G2,L2,T2. ❨G,L,T❩ ⬂* ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G1 #G #L1 #L #T1 #T #H1 #G2 #L2 #T2 #H @(fqus_ind … H) -G2 -L2 -T2
/3 width=5 by fpbs_strap1, fquq_fpb/
qed-.

lemma fqus_fpbs_trans:
      ∀G,G2,L,L2,T,T2. ❨G,L,T❩ ≥ ❨G2,L2,T2❩ →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ⬂* ❨G,L,T❩ → ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
#G #G2 #L #L2 #T #T2 #H1 #G1 #L1 #T1 #H @(fqus_ind_dx … H) -G1 -L1 -T1
/3 width=5 by fpbs_strap2, fquq_fpb/
qed-.
