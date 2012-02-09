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

include "Basic_2/reducibility/cnf_lift.ma".
include "Basic_2/computation/acp.ma".
include "Basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERMS *****************************)

(* Advanced properties ******************************************************)

lemma csn_acp: acp cpr (eq …) (csn …).
@mk_acp
[ /2 width=1/
| /2 width=3/
| /2 width=5/
| @cnf_lift
]
qed.

lemma csn_abst: ∀L,W. L ⊢ ⬇* W → ∀I,V,T. L. ⓑ{I} V ⊢ ⬇* T → L ⊢ ⬇* ⓛW. T.
#L #W #HW elim HW -W #W #_ #IHW #I #V #T #HT @(csn_ind … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpr_inv_abst1 … H1 I V) -H1
#W0 #T0 #HLW0 #HLT0 #H destruct
elim (eq_false_inv_tpair … H2) -H2
[ /3 width=5/
| -HLW0 * #H destruct /3 width=1/
]
qed.

(* Relocation properties ****************************************************)

(* Basic_1: was: sn3_lift *)
lemma csn_lift: ∀L2,L1,T1,d,e. L1 ⊢ ⬇* T1 →
                ∀T2. ⇩[d, e] L2 ≡ L1 → ⇧[d, e] T1 ≡ T2 → L2 ⊢ ⬇* T2.
#L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL21 #HT12
@csn_intro #T #HLT2 #HT2
elim (cpr_inv_lift … HL21 … HT12 … HLT2) -HLT2 #T0 #HT0 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_mono … HT0 … HT12) in HT2; -T0 /2 width=1/
qed.

(* Basic_1: was: sn3_gen_lift *)
lemma csn_inv_lift: ∀L2,L1,T1,d,e. L1 ⊢ ⬇* T1 →
                    ∀T2. ⇩[d, e] L1 ≡ L2 → ⇧[d, e] T2 ≡ T1 → L2 ⊢ ⬇* T2.
#L2 #L1 #T1 #d #e #H elim H -T1 #T1 #_ #IHT1 #T2 #HL12 #HT21
@csn_intro #T #HLT2 #HT2
elim (lift_total T d e) #T0 #HT0
lapply (cpr_lift … HL12 … HT21 … HT0 HLT2) -HLT2 #HLT10
@(IHT1 … HLT10) // -L1 -L2 #H destruct
>(lift_inj … HT0 … HT21) in HT2; -T0 /2 width=1/
qed.
