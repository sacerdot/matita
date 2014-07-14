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

include "basic_2/static/aaa_aaa.ma".
include "basic_2/static/lsuba.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ATOMIC ARITY ASSIGNMENT *****************)

(* Properties concerning atomic arity assignment ****************************)

lemma lsuba_aaa_conf: ∀G,L1,V,A. ⦃G, L1⦄ ⊢ V ⁝ A →
                      ∀L2. G ⊢ L1 ⫃⁝ L2 → ⦃G, L2⦄ ⊢ V ⁝ A.
#G #L1 #V #A #H elim H -G -L1 -V -A
[ //
| #I #G #L1 #K1 #V #A #i #HLK1 #HV #IHV #L2 #HL12
  elim (lsuba_drop_O1_conf … HL12 … HLK1) -L1 #X #H #HLK2
  elim (lsuba_inv_pair1 … H) -H * #K2
  [ #HK12 #H destruct /3 width=5 by aaa_lref/
  | #W0 #V0 #A0 #HV0 #HW0 #_ #H1 #H2 #H3 destruct
    lapply (aaa_mono … HV0 … HV) #H destruct -V0 /2 width=5 by aaa_lref/
  ]
| /4 width=2 by lsuba_pair, aaa_abbr/
| /4 width=1 by lsuba_pair, aaa_abst/
| /3 width=3 by aaa_appl/
| /3 width=1 by aaa_cast/
]
qed-.

lemma lsuba_aaa_trans: ∀G,L2,V,A. ⦃G, L2⦄ ⊢ V ⁝ A →
                       ∀L1. G ⊢ L1 ⫃⁝ L2 → ⦃G, L1⦄ ⊢ V ⁝ A.
#G #L2 #V #A #H elim H -G -L2 -V -A
[ //
| #I #G #L2 #K2 #V #A #i #HLK2 #H1V #IHV #L1 #HL12
  elim (lsuba_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsuba_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct /3 width=5 by aaa_lref/
  | #V0 #A0 #HV0 #H2V #_ #H1 #H2 destruct
    lapply (aaa_mono … H2V … H1V) #H destruct -K2 /2 width=5 by aaa_lref/
  ]
| /4 width=2 by lsuba_pair, aaa_abbr/
| /4 width=1 by lsuba_pair, aaa_abst/
| /3 width=3 by aaa_appl/
| /3 width=1 by aaa_cast/
]
qed-.
