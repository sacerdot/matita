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

include "basic_2/rt_transition/fpb_aaa.ma".
include "basic_2/rt_computation/fpbs_fqup.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with atomic arity assignment for terms ************************)

lemma fpbs_aaa_conf:
      ∀G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫ →
      ∀A1. ❪G1,L1❫ ⊢ T1 ⁝ A1 → ∃A2. ❪G2,L2❫ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
[ /2 width=2 by ex_intro/
| #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #A #HA elim (IH1 … HA) -IH1 -A
  /2 width=8 by fpb_aaa_conf/
]
qed-.
