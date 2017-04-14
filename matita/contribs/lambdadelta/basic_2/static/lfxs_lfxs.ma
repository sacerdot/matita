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

(* Advanced properties ******************************************************)

lemma lfxs_inv_frees: ∀R,L1,L2,T. L1 ⦻*[R, T] L2 →
                      ∀f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → L1 ⦻*[R, cfull, f] L2.
#R #L1 #L2 #T * /3 width=6 by frees_mono, lexs_eq_repl_back/
qed-.

(* Basic_2A1: uses: llpx_sn_dec *)
lemma lfxs_dec: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                ∀L1,L2,T. Decidable (L1 ⦻*[R, T] L2).
#R #HR #L1 #L2 #T
elim (frees_total L1 T) #f #Hf
elim (lexs_dec R cfull HR … L1 L2 f)
/4 width=3 by lfxs_inv_frees, cfull_dec, ex2_intro, or_intror, or_introl/
qed-.

lemma lfxs_pair_sn_split: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                          lexs_frees_confluent … R1 cfull →
                          ∀L1,L2,V. L1 ⦻*[R1, V] L2 → ∀I,T.
                          ∃∃L. L1 ⦻*[R1, ②{I}V.T] L & L ⦻*[R2, V] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #V * #f #Hf #HL12 * [ #p ] #I #T
[ elim (frees_total L1 (ⓑ{p,I}V.T)) #g #Hg
  elim (frees_inv_bind … Hg) #y1 #y2 #H #_ #Hy
| elim (frees_total L1 (ⓕ{I}V.T)) #g #Hg
  elim (frees_inv_flat … Hg) #y1 #y2 #H #_ #Hy
]
lapply(frees_mono … H … Hf) -H #H1
lapply (sor_eq_repl_back1 … Hy … H1) -y1 #Hy
lapply (sor_inv_sle_sn … Hy) -y2 #Hfg
elim (lexs_sle_split … HR1 HR2 … HL12 … Hfg) -HL12 #L #HL1 #HL2
lapply (sle_lexs_trans … HL1 … Hfg) // #H
elim (HR … Hf … H) -HR -Hf -H
/4 width=7 by sle_lexs_trans, ex2_intro/
qed-.

lemma lfxs_flat_dx_split: ∀R1,R2. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                          lexs_frees_confluent … R1 cfull →
                          ∀L1,L2,T. L1 ⦻*[R1, T] L2 → ∀I,V.
                          ∃∃L. L1 ⦻*[R1, ⓕ{I}V.T] L & L ⦻*[R2, T] L2.
#R1 #R2 #HR1 #HR2 #HR #L1 #L2 #T * #f #Hf #HL12 #I #V
elim (frees_total L1 (ⓕ{I}V.T)) #g #Hg
elim (frees_inv_flat … Hg) #y1 #y2 #_ #H #Hy
lapply(frees_mono … H … Hf) -H #H2
lapply (sor_eq_repl_back2 … Hy … H2) -y2 #Hy
lapply (sor_inv_sle_dx … Hy) -y1 #Hfg
elim (lexs_sle_split … HR1 HR2 … HL12 … Hfg) -HL12 #L #HL1 #HL2
lapply (sle_lexs_trans … HL1 … Hfg) // #H
elim (HR … Hf … H) -HR -Hf -H
/4 width=7 by sle_lexs_trans, ex2_intro/
qed-.

(* Main properties **********************************************************)

(* Basic_2A1: uses: llpx_sn_bind llpx_sn_bind_O *)
theorem lfxs_bind: ∀R,p,I,L1,L2,V1,V2,T.
                   L1 ⦻*[R, V1] L2 → L1.ⓑ{I}V1 ⦻*[R, T] L2.ⓑ{I}V2 →
                   L1 ⦻*[R, ⓑ{p,I}V1.T] L2.
#R #p #I #L1 #L2 #V1 #V2 #T * #f1 #HV #Hf1 * #f2 #HT #Hf2
elim (lexs_fwd_pair … Hf2) -Hf2 #Hf2 #_ elim (sor_isfin_ex f1 (⫱f2))
/3 width=7 by frees_fwd_isfin, frees_bind, lexs_join, isfin_tl, ex2_intro/
qed.

(* Basic_2A1: llpx_sn_flat *)
theorem lfxs_flat: ∀R,I,L1,L2,V,T.
                   L1 ⦻*[R, V] L2 → L1 ⦻*[R, T] L2 →
                   L1 ⦻*[R, ⓕ{I}V.T] L2.
#R #I #L1 #L2 #V #T * #f1 #HV #Hf1 * #f2 #HT #Hf2 elim (sor_isfin_ex f1 f2)
/3 width=7 by frees_fwd_isfin, frees_flat, lexs_join, ex2_intro/
qed.

theorem lfxs_conf: ∀R1,R2.
                   lexs_frees_confluent R1 cfull →
                   lexs_frees_confluent R2 cfull →
                   R_confluent2_lfxs R1 R2 R1 R2 →
                   ∀T. confluent2 … (lfxs R1 T) (lfxs R2 T).
#R1 #R2 #HR1 #HR2 #HR12 #T #L0 #L1 * #f1 #Hf1 #HL01 #L2 * #f #Hf #HL02
lapply (frees_mono … Hf1 … Hf) -Hf1 #Hf12
lapply (lexs_eq_repl_back … HL01 … Hf12) -f1 #HL01
elim (lexs_conf … HL01 … HL02) /2 width=3 by ex2_intro/ [ | -HL01 -HL02 ]
[ #L #HL1 #HL2
  elim (HR1 … Hf … HL01) -HL01 #f1 #Hf1 #H1
  elim (HR2 … Hf … HL02) -HL02 #f2 #Hf2 #H2
  lapply (sle_lexs_trans … HL1 … H1) // -HL1 -H1 #HL1
  lapply (sle_lexs_trans … HL2 … H2) // -HL2 -H2 #HL2
  /3 width=5 by ex2_intro/
| #g #I #K0 #V0 #n #HLK0 #Hgf #V1 #HV01 #V2 #HV02 #K1 #HK01 #K2 #HK02
  elim (frees_drops_next … Hf … HLK0 … Hgf) -Hf -HLK0 -Hgf #g0 #Hg0 #H0
  lapply (sle_lexs_trans … HK01 … H0) // -HK01 #HK01
  lapply (sle_lexs_trans … HK02 … H0) // -HK02 #HK02
  elim (HR12 … HV01 … HV02 K1 … K2) /2 width=3 by ex2_intro/
]
qed-.

(* Negated inversion lemmas *************************************************)

(* Basic_2A1: uses: nllpx_sn_inv_bind nllpx_sn_inv_bind_O *)
lemma lfnxs_inv_bind: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                      ∀p,I,L1,L2,V,T. (L1 ⦻*[R, ⓑ{p,I}V.T] L2 → ⊥) →
                      (L1 ⦻*[R, V] L2 → ⊥) ∨ (L1.ⓑ{I}V ⦻*[R, T] L2.ⓑ{I}V → ⊥).
#R #HR #p #I #L1 #L2 #V #T #H elim (lfxs_dec … HR L1 L2 V)
/4 width=2 by lfxs_bind, or_intror, or_introl/
qed-.

(* Basic_2A1: uses: nllpx_sn_inv_flat *)
lemma lfnxs_inv_flat: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                      ∀I,L1,L2,V,T. (L1 ⦻*[R, ⓕ{I}V.T] L2 → ⊥) →
                      (L1 ⦻*[R, V] L2 → ⊥) ∨ (L1 ⦻*[R, T] L2 → ⊥).
#R #HR #I #L1 #L2 #V #T #H elim (lfxs_dec … HR L1 L2 V)
/4 width=1 by lfxs_flat, or_intror, or_introl/
qed-.
