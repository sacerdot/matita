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
include "ground_2/relocation/rtmap_sor.ma".
include "basic_2/relocation/lexs.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Main properties **********************************************************)

theorem lexs_trans_gen (RN1) (RP1) (RN2) (RP2) (RN) (RP) (f):
                       lexs_transitive RN1 RN2 RN RN1 RP1 →
                       lexs_transitive RP1 RP2 RP RN1 RP1 →
                       ∀L1,L0. L1 ⦻*[RN1, RP1, f] L0 →
                       ∀L2. L0 ⦻*[RN2, RP2, f] L2 →
                       L1 ⦻*[RN, RP, f] L2.
#RN1 #RP1 #RN2 #RP2 #RN #RP #f #HN #HP #L1 #L0 #H elim H -f -L1 -L0
[ #f #L2 #H >(lexs_inv_atom1 … H) -L2 //
| #f #I #K1 #K #V1 #V #HK1 #HV1 #IH #L2 #H elim (lexs_inv_next1 … H) -H
  #K2 #V2 #HK2 #HV2 #H destruct /4 width=6 by lexs_next/
| #f #I #K1 #K #V1 #V #HK1 #HV1 #IH #L2 #H elim (lexs_inv_push1 … H) -H
  #K2 #V2 #HK2 #HV2 #H destruct /4 width=6 by lexs_push/
]
qed-.

(* Basic_2A1: includes: lpx_sn_trans *)
theorem lexs_trans (RN) (RP) (f): lexs_transitive RN RN RN RN RP →
                                  lexs_transitive RP RP RP RN RP →
                                  Transitive … (lexs RN RP f).
/2 width=9 by lexs_trans_gen/ qed-.

(* Basic_2A1: includes: lpx_sn_conf *)
theorem lexs_conf (RN1) (RP1) (RN2) (RP2): lexs_confluent RN1 RN2 RN1 RP1 RN2 RP2 →
                                           lexs_confluent RP1 RP2 RN1 RP1 RN2 RP2 →
                                           ∀f. confluent2 … (lexs RN1 RP1 f) (lexs RN2 RP2 f).
#RN1 #RP1 #RN2 #RP2 #HRN #HRP #f #L0
generalize in match f; -f elim L0 -L0
[ #f #L1 #HL01 #L2 #HL02 -HRN -HRP
  lapply (lexs_inv_atom1 … HL01) -HL01 #H destruct
  lapply (lexs_inv_atom1 … HL02) -HL02 #H destruct
  /2 width=3 by ex2_intro/
| #K0 #I #V0 #IH #f #L1 #HL01 #L2 #HL02
  elim (pn_split f) * #g #H destruct
  [ elim (lexs_inv_push1 … HL01) -HL01 #K1 #V1 #HK01 #HV01 #H destruct
    elim (lexs_inv_push1 … HL02) -HL02 #K2 #V2 #HK02 #HV02 #H destruct
    elim (IH … HK01 … HK02) -IH #K #HK1 #HK2
    elim (HRP … HV01 … HV02 … HK01 … HK02) -HRP -HRN -K0 -V0
    /3 width=5 by lexs_push, ex2_intro/
  | elim (lexs_inv_next1 … HL01) -HL01 #K1 #V1 #HK01 #HV01 #H destruct
    elim (lexs_inv_next1 … HL02) -HL02 #K2 #V2 #HK02 #HV02 #H destruct
    elim (IH … HK01 … HK02) -IH #K #HK1 #HK2
    elim (HRN … HV01 … HV02 … HK01 … HK02) -HRN -HRP -K0 -V0
    /3 width=5 by lexs_next, ex2_intro/
  ]
]
qed-.

theorem lexs_canc_sn: ∀RN,RP,f. Transitive … (lexs RN RP f) →
                                symmetric … (lexs RN RP f) →
                                left_cancellable … (lexs RN RP f).
/3 width=3 by/ qed-.

theorem lexs_canc_dx: ∀RN,RP,f. Transitive … (lexs RN RP f) →
                                symmetric … (lexs RN RP f) →
                                right_cancellable … (lexs RN RP f).
/3 width=3 by/ qed-.

lemma lexs_meet: ∀RN,RP,L1,L2.
                 ∀f1. L1 ⦻*[RN, RP, f1] L2 →
                 ∀f2. L1 ⦻*[RN, RP, f2] L2 →
                 ∀f. f1 ⋒ f2 ≡ f → L1 ⦻*[RN, RP, f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I #L1 #L2 #V1 #V2 #_ #HV12 #IH #f2 #H #f #Hf
elim (pn_split f2) * #g2 #H2 destruct
try elim (lexs_inv_push … H) try elim (lexs_inv_next … H) -H
[ elim (sand_inv_npx … Hf) | elim (sand_inv_nnx … Hf)
| elim (sand_inv_ppx … Hf) | elim (sand_inv_pnx … Hf)
] -Hf /3 width=5 by lexs_next, lexs_push/
qed-.

lemma lexs_join: ∀RN,RP,L1,L2.
                 ∀f1. L1 ⦻*[RN, RP, f1] L2 →
                 ∀f2. L1 ⦻*[RN, RP, f2] L2 →
                 ∀f. f1 ⋓ f2 ≡ f → L1 ⦻*[RN, RP, f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I #L1 #L2 #V1 #V2 #_ #HV12 #IH #f2 #H #f #Hf
elim (pn_split f2) * #g2 #H2 destruct
try elim (lexs_inv_push … H) try elim (lexs_inv_next … H) -H
[ elim (sor_inv_npx … Hf) | elim (sor_inv_nnx … Hf)
| elim (sor_inv_ppx … Hf) | elim (sor_inv_pnx … Hf)
] -Hf /3 width=5 by lexs_next, lexs_push/
qed-.
