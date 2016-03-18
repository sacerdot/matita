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
include "basic_2/grammar/lenv_weight.ma".
include "basic_2/relocation/lexs.ma".

(* GENERAL ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Main properties **********************************************************)

(* Basic_2A1: includes: lpx_sn_trans *)
theorem lexs_trans (RN) (RP) (f): lexs_transitive RN RN RN RP →
                                  lexs_transitive RP RP RN RP →
                                  Transitive … (lexs RN RP f).
#RN #RP #f #HN #HP #L1 #L0 #H elim H -L1 -L0 -f
[ #f #L2 #H >(lexs_inv_atom1 … H) -L2 //
| #I #K1 #K #V1 #V #f #HK1 #HV1 #IH #L2 #H elim (lexs_inv_next1 … H) -H
  #K2 #V2 #HK2 #HV2 #H destruct /4 width=6 by lexs_next/
| #I #K1 #K #V1 #V #f #HK1 #HV1 #IH #L2 #H elim (lexs_inv_push1 … H) -H
  #K2 #V2 #HK2 #HV2 #H destruct /4 width=6 by lexs_push/
]
qed-.

(* Basic_2A1: includes: lpx_sn_conf *)
theorem lexs_conf: ∀RN1,RP1,RN2,RP2.
                   lpx_sn_confluent RN1 RN2 RN1 RP1 RN2 RP2 →
                   lpx_sn_confluent RP1 RP2 RN1 RP1 RN2 RP2 →
                   ∀f. confluent2 … (lexs RN1 RP1 f) (lexs RN2 RP2 f).
#RN1 #RP1 #RN2 #RP2 #HRN #HRP #f #L0 generalize in match f; -f
@(f_ind … lw … L0) -L0 #x #IH *
[ #_ #f #X1 #H1 #X2 #H2 -x
  >(lexs_inv_atom1 … H1) -X1
  >(lexs_inv_atom1 … H2) -X2 /2 width=3 by lexs_atom, ex2_intro/
| #L0 #I #V0 #Hx #f elim (pn_split f) *
  #g #H #X1 #H1 #X2 #H2 destruct
  [ elim (lexs_inv_push1 … H1) -H1 #L1 #V1 #HL01 #HV01 #H destruct
    elim (lexs_inv_push1 … H2) -H2 #L2 #V2 #HL02 #HV02 #H destruct
    elim (IH … HL01 … HL02) -IH // #L #HL1 #HL2
    elim (HRP … HV01 … HV02 … HL01 … HL02) -L0 -V0 /3 width=5 by lexs_push, ex2_intro/
  | elim (lexs_inv_next1 … H1) -H1 #L1 #V1 #HL01 #HV01 #H destruct
    elim (lexs_inv_next1 … H2) -H2 #L2 #V2 #HL02 #HV02 #H destruct
    elim (IH … HL01 … HL02) -IH // #L #HL1 #HL2
    elim (HRN … HV01 … HV02 … HL01 … HL02) -L0 -V0 /3 width=5 by lexs_next, ex2_intro/
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

theorem lexs_meet: ∀RN,RP,L1,L2,f1. L1 ⦻*[RN, RP, f1] L2 →
                   ∀f2. L1 ⦻*[RN, RP, f2] L2 →
                   ∀f. f1 ⋒ f2 ≡ f → L1 ⦻*[RN, RP, f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -L1 -L2 -f1 //
#I #L1 #L2 #V1 #V2 #f1 #_ #H1V #IH #f2 elim (pn_split f2) *
#g2 #H #H2 #f #Hf destruct
[1,3: elim (lexs_inv_push … H2) |2,4: elim (lexs_inv_next … H2) ] -H2
#H2 #H2V #_
[ elim (sand_inv_npx … Hf) | elim (sand_inv_ppx … Hf) | elim (sand_inv_nnx … Hf) | elim (sand_inv_pnx … Hf) ] -Hf
/3 width=5 by lexs_next, lexs_push/
qed-.

theorem lexs_join: ∀RN,RP,L1,L2,f1. L1 ⦻*[RN, RP, f1] L2 →
                   ∀f2. L1 ⦻*[RN, RP, f2] L2 →
                   ∀f. f1 ⋓ f2 ≡ f → L1 ⦻*[RN, RP, f] L2.
#RN #RP #L1 #L2 #f1 #H elim H -L1 -L2 -f1 //
#I #L1 #L2 #V1 #V2 #f1 #_ #H1V #IH #f2 elim (pn_split f2) *
#g2 #H #H2 #f #Hf destruct
[1,3: elim (lexs_inv_push … H2) |2,4: elim (lexs_inv_next … H2) ] -H2
#H2 #H2V #_
[ elim (sor_inv_npx … Hf) | elim (sor_inv_ppx … Hf) | elim (sor_inv_nnx … Hf) | elim (sor_inv_pnx … Hf) ] -Hf
/3 width=5 by lexs_next, lexs_push/
qed-.
