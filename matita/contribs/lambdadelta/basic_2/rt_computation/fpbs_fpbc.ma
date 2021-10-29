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

include "basic_2/rt_transition/fpbc_feqg.ma".
include "basic_2/rt_transition/fpbc_fpb.ma".
include "basic_2/rt_computation/fpbs_feqg.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with proper parallel rst-reduction on closures ****************)

lemma fpbc_fpbs:
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ≻ ❨G2,L2,T2❩ →
      ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩.
/3 width=1 by fpb_fpbs, fpbc_fwd_fpb/ qed.

(* Inversion lemmas with proper parallel rst-reduction on closures **********)

lemma fpbs_inv_fpbc_sn:
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ →
      ∨∨ ❨G1,L1,T1❩ ≅ ❨G2,L2,T2❩
       | ∃∃G,L,T. ❨G1,L1,T1❩ ≻ ❨G,L,T❩ & ❨G,L,T❩ ≥ ❨G2,L2,T2❩.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
[ /3 width=1 by feqg_refl, or_introl/
| #G #G2 #L #L2 #T #T2 #_ #H2 * [ #H1 | * #G0 #L0 #T0 #H10 #H0 ]
  elim (fpb_inv_fpbc … H2) -H2 #H2
  [ /3 width=5 by feqg_trans, or_introl/
  | lapply (feqg_fpbc_trans … H1 … H2) -G -L -T //
    /3 width=5 by fpb_fpbs, ex2_3_intro, or_intror/
  | /4 width=12 by fpbs_feqg_trans, ex2_3_intro, or_intror/
  | /5 width=9 by fpbs_strap1, fpbc_fwd_fpb, ex2_3_intro, or_intror/
  ]
]
qed-.
