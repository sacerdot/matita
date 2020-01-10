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

include "ground_2/relocation/rtmap_sand.ma".
include "static_2/relocation/drops.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Main properties **********************************************************)

theorem sex_trans_gen (RN1) (RP1) (RN2) (RP2) (RN) (RP):
                      ∀L1,f.
                      (∀g,I,K,n. ⇩[n] L1 ≘ K.ⓘ[I] → ↑g = ⫱*[n] f → sex_transitive RN1 RN2 RN RN1 RP1 g K I) →
                      (∀g,I,K,n. ⇩[n] L1 ≘ K.ⓘ[I] → ⫯g = ⫱*[n] f → sex_transitive RP1 RP2 RP RN1 RP1 g K I) →
                      ∀L0. L1 ⪤[RN1,RP1,f] L0 →
                      ∀L2. L0 ⪤[RN2,RP2,f] L2 →
                      L1 ⪤[RN,RP,f] L2.
#RN1 #RP1 #RN2 #RP2 #RN #RP #L1 elim L1 -L1
[ #f #_ #_ #L0 #H1 #L2 #H2
  lapply (sex_inv_atom1 … H1) -H1 #H destruct
  lapply (sex_inv_atom1 … H2) -H2 #H destruct
  /2 width=1 by sex_atom/
| #K1 #I1 #IH #f elim (pn_split f) * #g #H destruct
  #HN #HP #L0 #H1 #L2 #H2
  [ elim (sex_inv_push1 … H1) -H1 #I0 #K0 #HK10 #HI10 #H destruct
    elim (sex_inv_push1 … H2) -H2 #I2 #K2 #HK02 #HI02 #H destruct
    lapply (HP … 0 … HI10 … HK10 … HI02) -HI10 -HI02 /2 width=2 by drops_refl/ #HI12
    lapply (IH … HK10 … HK02) -IH -K0 /3 width=3 by sex_push, drops_drop/
  | elim (sex_inv_next1 … H1) -H1 #I0 #K0 #HK10 #HI10 #H destruct
    elim (sex_inv_next1 … H2) -H2 #I2 #K2 #HK02 #HI02 #H destruct
    lapply (HN … 0 … HI10 … HK10 … HI02) -HI10 -HI02 /2 width=2 by drops_refl/ #HI12
    lapply (IH … HK10 … HK02) -IH -K0 /3 width=3 by sex_next, drops_drop/
  ]
]
qed-.

theorem sex_trans (RN) (RP) (f): (∀g,I,K. sex_transitive RN RN RN RN RP g K I) →
                                 (∀g,I,K. sex_transitive RP RP RP RN RP g K I) →
                                 Transitive … (sex RN RP f).
/2 width=9 by sex_trans_gen/ qed-.

theorem sex_trans_id_cfull: ∀R1,R2,R3,L1,L,f. L1 ⪤[R1,cfull,f] L → 𝐈❪f❫ →
                            ∀L2. L ⪤[R2,cfull,f] L2 → L1 ⪤[R3,cfull,f] L2.
#R1 #R2 #R3 #L1 #L #f #H elim H -L1 -L -f
[ #f #Hf #L2 #H >(sex_inv_atom1 … H) -L2 // ]
#f #I1 #I #K1 #K #HK1 #_ #IH #Hf #L2 #H
[ elim (isid_inv_next … Hf) | lapply (isid_inv_push … Hf ??) ] -Hf [5: |*: // ] #Hf
elim (sex_inv_push1 … H) -H #I2 #K2 #HK2 #_ #H destruct
/3 width=1 by sex_push/
qed-.

theorem sex_conf (RN1) (RP1) (RN2) (RP2):
                 ∀L,f.
                 (∀g,I,K,n. ⇩[n] L ≘ K.ⓘ[I] → ↑g = ⫱*[n] f → R_pw_confluent2_sex RN1 RN2 RN1 RP1 RN2 RP2 g K I) →
                 (∀g,I,K,n. ⇩[n] L ≘ K.ⓘ[I] → ⫯g = ⫱*[n] f → R_pw_confluent2_sex RP1 RP2 RN1 RP1 RN2 RP2 g K I) →
                 pw_confluent2 … (sex RN1 RP1 f) (sex RN2 RP2 f) L.
#RN1 #RP1 #RN2 #RP2 #L elim L -L
[ #f #_ #_ #L1 #H1 #L2 #H2 >(sex_inv_atom1 … H1) >(sex_inv_atom1 … H2) -H2 -H1
  /2 width=3 by sex_atom, ex2_intro/
| #L #I0 #IH #f elim (pn_split f) * #g #H destruct
  #HN #HP #Y1 #H1 #Y2 #H2
  [ elim (sex_inv_push1 … H1) -H1 #I1 #L1 #HL1 #HI01 #H destruct
    elim (sex_inv_push1 … H2) -H2 #I2 #L2 #HL2 #HI02 #H destruct
    elim (HP … 0 … HI01 … HI02 … HL1 … HL2) -HI01 -HI02 /2 width=2 by drops_refl/ #I #HI1 #HI2
    elim (IH … HL1 … HL2) -IH -HL1 -HL2 /3 width=5 by drops_drop, sex_push, ex2_intro/
  | elim (sex_inv_next1 … H1) -H1 #I1 #L1 #HL1 #HI01 #H destruct
    elim (sex_inv_next1 … H2) -H2 #I2 #L2 #HL2 #HI02 #H destruct
    elim (HN … 0 … HI01 … HI02 … HL1 … HL2) -HI01 -HI02 /2 width=2 by drops_refl/ #I #HI1 #HI2
    elim (IH … HL1 … HL2) -IH -HL1 -HL2 /3 width=5 by drops_drop, sex_next, ex2_intro/
  ]
]
qed-.

theorem sex_canc_sn: ∀RN,RP,f. Transitive … (sex RN RP f) →
                               symmetric … (sex RN RP f) →
                               left_cancellable … (sex RN RP f).
/3 width=3 by/ qed-.

theorem sex_canc_dx: ∀RN,RP,f. Transitive … (sex RN RP f) →
                               symmetric … (sex RN RP f) →
                               right_cancellable … (sex RN RP f).
/3 width=3 by/ qed-.

lemma sex_meet: ∀RN,RP,L1,L2.
                ∀f1. L1 ⪤[RN,RP,f1] L2 →
                ∀f2. L1 ⪤[RN,RP,f2] L2 →
                ∀f. f1 ⋒ f2 ≘ f → L1 ⪤[RN,RP,f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I1 #I2 #L1 #L2 #_ #HI12 #IH #f2 #H #f #Hf
elim (pn_split f2) * #g2 #H2 destruct
try elim (sex_inv_push … H) try elim (sex_inv_next … H) -H
[ elim (sand_inv_npx … Hf) | elim (sand_inv_nnx … Hf)
| elim (sand_inv_ppx … Hf) | elim (sand_inv_pnx … Hf)
] -Hf /3 width=5 by sex_next, sex_push/
qed-.

lemma sex_join: ∀RN,RP,L1,L2.
                ∀f1. L1 ⪤[RN,RP,f1] L2 →
                ∀f2. L1 ⪤[RN,RP,f2] L2 →
                ∀f. f1 ⋓ f2 ≘ f → L1 ⪤[RN,RP,f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I1 #I2 #L1 #L2 #_ #HI12 #IH #f2 #H #f #Hf
elim (pn_split f2) * #g2 #H2 destruct
try elim (sex_inv_push … H) try elim (sex_inv_next … H) -H
[ elim (sor_inv_npx … Hf) | elim (sor_inv_nnx … Hf)
| elim (sor_inv_ppx … Hf) | elim (sor_inv_pnx … Hf)
] -Hf /3 width=5 by sex_next, sex_push/
qed-.
