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

include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/static/frees_fqup.ma".
include "basic_2/static/frees_frees.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

axiom frees_lexs_conf_sle: ∀RN,RP,f1,L1,T. L1 ⊢ 𝐅*⦃T⦄ ≡ f1 →
                           ∀L2. L1 ⦻*[RN, RP, f1] L2 →
                           ∃∃f2. L2 ⊢ 𝐅*⦃T⦄ ≡ f2 & f2 ⊆ f1.

theorem lfxs_conf: ∀R. R_confluent2_lfxs R R R R →
                   ∀T. confluent … (lfxs R T).
#R #H1R #T #L0 #L1 * #f1 #Hf1 #HL01 #L2 * #f #Hf #HL02
lapply (frees_mono … Hf1 … Hf) -Hf1 #Hf12
lapply (lexs_eq_repl_back … HL01 … Hf12) -f1 #HL01
elim (lexs_conf … HL01 … HL02) /2 width=3 by ex2_intro/ [ | -HL01 -HL02 ]
[ #L #HL1 #HL2
  elim (frees_lexs_conf_sle … Hf … HL01) -HL01 #f1 #Hf1 #H1
  elim (frees_lexs_conf_sle … Hf … HL02) -HL02 #f2 #Hf2 #H2
  lapply (sle_lexs_trans … HL1 … H1) // -HL1 -H1 #HL1
  lapply (sle_lexs_trans … HL2 … H2) // -HL2 -H2 #HL2
  /3 width=5 by ex2_intro/
| #g #I #K0 #V0 #n #HLK0 #Hgf #V1 #HV01 #V2 #HV02 #K1 #HK01 #K2 #HK02
  elim (frees_drops_next … Hf … HLK0 … Hgf) -Hf -HLK0 -Hgf #g0 #Hg0 #H0
  lapply (sle_lexs_trans … HK01 … H0) // -HK01 #HK01
  lapply (sle_lexs_trans … HK02 … H0) // -HK02 #HK02
  elim (H1R … HV01 … HV02 K1 … K2) /2 width=3 by ex2_intro/
]
qed-.

(*
lemma pippo: ∀R1,R2,RP1,RP2. R_confluent_lfxs R1 R2 RP1 RP2 →
             lexs_confluent R1 R2 RP1 cfull RP2 cfull.
#R1 #R2 #RP1 #RP2 #HR #f #L0 #T0 #T1 #HT01 #T2 #HT02 #L1 #HL01 #L2
#HL02
*)
