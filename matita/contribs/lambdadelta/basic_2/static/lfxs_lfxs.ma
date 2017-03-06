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

include "basic_2/relocation/lexs_lexs.ma".
include "basic_2/static/frees_fqup.ma".
include "basic_2/static/frees_frees.ma".
include "basic_2/static/lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Main properties **********************************************************)

theorem lfxs_bind: ∀R,p,I,L1,L2,V1,V2,T.
                   L1 ⦻*[R, V1] L2 → L1.ⓑ{I}V1 ⦻*[R, T] L2.ⓑ{I}V2 →
                   L1 ⦻*[R, ⓑ{p,I}V1.T] L2.
#R #p #I #L1 #L2 #V1 #V2 #T * #f1 #HV #Hf1 * #f2 #HT #Hf2
elim (lexs_fwd_pair … Hf2) -Hf2 #Hf2 #_ elim (sor_isfin_ex f1 (⫱f2))
/3 width=7 by frees_fwd_isfin, frees_bind, lexs_join, isfin_tl, ex2_intro/
qed.

theorem lfxs_flat: ∀R,I,L1,L2,V,T.
                   L1 ⦻*[R, V] L2 → L1 ⦻*[R, T] L2 →
                   L1 ⦻*[R, ⓕ{I}V.T] L2.
#R #I #L1 #L2 #V #T * #f1 #HV #Hf1 * #f2 #HT #Hf2 elim (sor_isfin_ex f1 f2)
/3 width=7 by frees_fwd_isfin, frees_flat, lexs_join, ex2_intro/
qed.

theorem lfxs_conf: ∀R. lexs_frees_confluent R cfull →
                   R_confluent2_lfxs R R R R →
                   ∀T. confluent … (lfxs R T).
#R #H1R #H2R #T #L0 #L1 * #f1 #Hf1 #HL01 #L2 * #f #Hf #HL02
lapply (frees_mono … Hf1 … Hf) -Hf1 #Hf12
lapply (lexs_eq_repl_back … HL01 … Hf12) -f1 #HL01
elim (lexs_conf … HL01 … HL02) /2 width=3 by ex2_intro/ [ | -HL01 -HL02 ]
[ #L #HL1 #HL2
  elim (H1R … Hf … HL01) -HL01 #f1 #Hf1 #H1
  elim (H1R … Hf … HL02) -HL02 #f2 #Hf2 #H2
  lapply (sle_lexs_trans … HL1 … H1) // -HL1 -H1 #HL1
  lapply (sle_lexs_trans … HL2 … H2) // -HL2 -H2 #HL2
  /3 width=5 by ex2_intro/
| #g #I #K0 #V0 #n #HLK0 #Hgf #V1 #HV01 #V2 #HV02 #K1 #HK01 #K2 #HK02
  elim (frees_drops_next … Hf … HLK0 … Hgf) -Hf -HLK0 -Hgf #g0 #Hg0 #H0
  lapply (sle_lexs_trans … HK01 … H0) // -HK01 #HK01
  lapply (sle_lexs_trans … HK02 … H0) // -HK02 #HK02
  elim (H2R … HV01 … HV02 K1 … K2) /2 width=3 by ex2_intro/
]
qed-.
