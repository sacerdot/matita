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

include "ground/lib/star.ma".
include "static_2/relocation/sex.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

definition s_rs_transitive_isid: relation (relation3 lenv bind bind) ≝ λRN,RP.
                                 ∀f. 𝐈❪f❫ → s_rs_transitive … RP (λ_.sex RN RP f).

(* Properties with transitive closure ***************************************)

lemma sex_tc_refl: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                   ∀f. reflexive … (TC … (sex RN RP f)).
/3 width=1 by sex_refl, TC_reflexive/ qed.

lemma sex_tc_next_sn: ∀RN,RP. c_reflexive … RN →
                      ∀f,I2,L1,L2. TC … (sex RN RP f) L1 L2 → ∀I1. RN L1 I1 I2 →
                      TC … (sex RN RP (↑f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRN #f #I2 #L1 #L2 #H @(TC_ind_dx ??????? H) -L1
/3 width=3 by sex_next, TC_strap, inj/
qed.

lemma sex_tc_next_dx: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                      ∀f,I1,I2,L1. (CTC … RN) L1 I1 I2 → ∀L2. L1 ⪤[RN,RP,f] L2 →
                      TC … (sex RN RP (↑f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRN #HRP #f #I1 #I2 #L1 #H elim H -I2
/4 width=5 by sex_refl, sex_next, step, inj/
qed.

lemma sex_tc_push_sn: ∀RN,RP. c_reflexive … RP →
                      ∀f,I2,L1,L2. TC … (sex RN RP f) L1 L2 → ∀I1. RP L1 I1 I2 →
                      TC … (sex RN RP (⫯f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRP #f #I2 #L1 #L2 #H @(TC_ind_dx ??????? H) -L1
/3 width=3 by sex_push, TC_strap, inj/
qed.

lemma sex_tc_push_dx: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                      ∀f,I1,I2,L1. (CTC … RP) L1 I1 I2 → ∀L2. L1 ⪤[RN,RP,f] L2 →
                      TC … (sex RN RP (⫯f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRN #HRP #f #I1 #I2 #L1 #H elim H -I2
/4 width=5 by sex_refl, sex_push, step, inj/
qed.

lemma sex_tc_inj_sn: ∀RN,RP,f,L1,L2. L1 ⪤[RN,RP,f] L2 → L1 ⪤[CTC … RN,RP,f] L2.
#RN #RP #f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by sex_push, sex_next, inj/
qed.

lemma sex_tc_inj_dx: ∀RN,RP,f,L1,L2. L1 ⪤[RN,RP,f] L2 → L1 ⪤[RN,CTC … RP,f] L2.
#RN #RP #f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by sex_push, sex_next, inj/
qed.

(* Main properties with transitive closure **********************************)

theorem sex_tc_next: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                     ∀f,I1,I2,L1. (CTC … RN) L1 I1 I2 → ∀L2. TC … (sex RN RP f) L1 L2 →
                     TC … (sex RN RP (↑f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRN #HRP #f #I1 #I2 #L1 #H elim H -I2
/4 width=5 by sex_tc_next_sn, sex_tc_refl, trans_TC/
qed.

theorem sex_tc_push: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                     ∀f,I1,I2,L1. (CTC … RP) L1 I1 I2 → ∀L2. TC … (sex RN RP f) L1 L2 →
                     TC … (sex RN RP (⫯f)) (L1.ⓘ[I1]) (L2.ⓘ[I2]).
#RN #RP #HRN #HRP #f #I1 #I2 #L1 #H elim H -I2
/4 width=5 by sex_tc_push_sn, sex_tc_refl, trans_TC/
qed.

(* Basic_2A1: uses: TC_lpx_sn_ind *)
theorem sex_tc_step_dx: ∀RN,RP. s_rs_transitive_isid RN RP →
                        ∀f,L1,L. L1 ⪤[RN,RP,f] L → 𝐈❪f❫ →
                        ∀L2. L ⪤[RN,CTC … RP,f] L2 → L1⪤ [RN,CTC … RP,f] L2.
#RN #RP #HRP #f #L1 #L #H elim H -f -L1 -L
[ #f #_ #Y #H -HRP >(sex_inv_atom1 … H) -Y // ]
#f #I1 #I #L1 #L #HL1 #HI1 #IH #Hf #Y #H
[ elim (isid_inv_next … Hf) -Hf //
| lapply (isid_inv_push … Hf ??) -Hf [3: |*: // ] #Hf
  elim (sex_inv_push1 … H) -H #I2 #L2 #HL2 #HI2 #H destruct
  @sex_push [ /2 width=1 by/ ] -L2 -IH
  @(TC_strap … HI1) -HI1
  @(HRP … HL1) // (**) (* auto fails *)
]
qed-.

(* Advanced properties ******************************************************)

lemma sex_tc_dx: ∀RN,RP. s_rs_transitive_isid RN RP →
                 ∀f. 𝐈❪f❫ → ∀L1,L2. TC … (sex RN RP f) L1 L2 → L1 ⪤[RN,CTC … RP,f] L2.
#RN #RP #HRP #f #Hf #L1 #L2 #H @(TC_ind_dx ??????? H) -L1
/3 width=3 by sex_tc_step_dx, sex_tc_inj_dx/
qed.

(* Advanced inversion lemmas ************************************************)

lemma sex_inv_tc_sn: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                     ∀f,L1,L2. L1 ⪤[CTC … RN,RP,f] L2 → TC … (sex RN RP f) L1 L2.
#RN #RP #HRN #HRP #f #L1 #L2 #H elim H -f -L1 -L2
/2 width=1 by sex_tc_next, sex_tc_push_sn, sex_atom, inj/
qed-.

lemma sex_inv_tc_dx: ∀RN,RP. c_reflexive … RN → c_reflexive … RP →
                     ∀f,L1,L2. L1 ⪤[RN,CTC … RP,f] L2 → TC … (sex RN RP f) L1 L2.
#RN #RP #HRN #HRP #f #L1 #L2 #H elim H -f -L1 -L2
/2 width=1 by sex_tc_push, sex_tc_next_sn, sex_atom, inj/
qed-.
