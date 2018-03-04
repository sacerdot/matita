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
include "basic_2/static/lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Advanced inversion lemmas ************************************************)

lemma lfxs_inv_frees: ∀R,L1,L2,T. L1 ⪤*[R, T] L2 →
                      ∀f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → L1 ⪤*[cext2 R, cfull, f] L2.
#R #L1 #L2 #T * /3 width=6 by frees_mono, lexs_eq_repl_back/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: llpx_sn_dec *)
lemma lfxs_dec: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                ∀L1,L2,T. Decidable (L1 ⪤*[R, T] L2).
#R #HR #L1 #L2 #T
elim (frees_total L1 T) #f #Hf
elim (lexs_dec (cext2 R) cfull … L1 L2 f)
/4 width=3 by lfxs_inv_frees, cfull_dec, ext2_dec, ex2_intro, or_intror, or_introl/
qed-.

(* Main properties **********************************************************)

(* Basic_2A1: uses: llpx_sn_bind llpx_sn_bind_O *)
theorem lfxs_bind: ∀R,p,I,L1,L2,V1,V2,T.
                   L1 ⪤*[R, V1] L2 → L1.ⓑ{I}V1 ⪤*[R, T] L2.ⓑ{I}V2 →
                   L1 ⪤*[R, ⓑ{p,I}V1.T] L2.
#R #p #I #L1 #L2 #V1 #V2 #T * #f1 #HV #Hf1 * #f2 #HT #Hf2
lapply (lexs_fwd_bind … Hf2) -Hf2 #Hf2 elim (sor_isfin_ex f1 (⫱f2))
/3 width=7 by frees_fwd_isfin, frees_bind, lexs_join, isfin_tl, ex2_intro/
qed.

(* Basic_2A1: llpx_sn_flat *)
theorem lfxs_flat: ∀R,I,L1,L2,V,T.
                   L1 ⪤*[R, V] L2 → L1 ⪤*[R, T] L2 →
                   L1 ⪤*[R, ⓕ{I}V.T] L2.
#R #I #L1 #L2 #V #T * #f1 #HV #Hf1 * #f2 #HT #Hf2 elim (sor_isfin_ex f1 f2)
/3 width=7 by frees_fwd_isfin, frees_flat, lexs_join, ex2_intro/
qed.

theorem lfxs_bind_void: ∀R,p,I,L1,L2,V,T.
                        L1 ⪤*[R, V] L2 → L1.ⓧ ⪤*[R, T] L2.ⓧ →
                        L1 ⪤*[R, ⓑ{p,I}V.T] L2.
#R #p #I #L1 #L2 #V #T * #f1 #HV #Hf1 * #f2 #HT #Hf2
lapply (lexs_fwd_bind … Hf2) -Hf2 #Hf2 elim (sor_isfin_ex f1 (⫱f2))
/3 width=7 by frees_fwd_isfin, frees_bind_void, lexs_join, isfin_tl, ex2_intro/
qed.

theorem lfxs_trans_gen: ∀R1,R2,R3. 
                        c_reflexive … R1 → c_reflexive … R2 →
                        lfxs_confluent R1 R2 → lfxs_transitive R1 R2 R3 →
                        ∀L1,T,L. L1 ⪤*[R1, T] L →
                        ∀L2. L ⪤*[R2, T] L2 → L1 ⪤*[R3, T] L2.
#R1 #R2 #R3 #H1R #H2R #H3R #H4R #L1 #T @(fqup_wf_ind_eq (Ⓣ) … (⋆) L1 T) -L1 -T
#G0 #L0 #T0 #IH #G #L1 * *
[ #s #HG #HL #HT #L #H1 #L2 #H2 destruct
  elim (lfxs_inv_sort … H1) -H1 *
  [ #H1 #H0 destruct
    >(lfxs_inv_atom_sn … H2) -L2 //
  | #I1 #I #K1 #K #HK1 #H1 #H0 destruct
    elim (lfxs_inv_sort_bind_sn … H2) -H2 #I2 #K2 #HK2 #H destruct
    /4 width=3 by lfxs_sort, fqu_fqup/
  ]
| * [ | #i ] #HG #HL #HT #L #H1 #L2 #H2 destruct
  [ elim (lfxs_inv_zero … H1) -H1 *
    [ #H1 #H0 destruct
      >(lfxs_inv_atom_sn … H2) -L2 //
    | #I #K1 #K #V1 #V #HK1 #H1 #H0 #H destruct
      elim (lfxs_inv_zero_pair_sn … H2) -H2 #K2 #V2 #HK2 #HV2 #H destruct
      /4 width=7 by lfxs_pair, fqu_fqup, fqu_lref_O/
    | #f1 #I #K1 #K #Hf1 #HK1 #H1 #H0 destruct
      elim (lfxs_inv_zero_unit_sn … H2) -H2 #f2 #K2 #Hf2 #HK2 #H destruct
      /5 width=8 by lfxs_unit, lexs_trans_id_cfull, lexs_eq_repl_back, isid_inv_eq_repl/
    ]
  | elim (lfxs_inv_lref … H1) -H1 *
    [ #H1 #H0 destruct
      >(lfxs_inv_atom_sn … H2) -L2 //
    | #I1 #I #K1 #K #HK1 #H1 #H0 destruct
      elim (lfxs_inv_lref_bind_sn … H2) -H2 #I2 #K2 #HK2 #H destruct
     /4 width=3 by lfxs_lref, fqu_fqup/
    ]
  ]
| #l #HG #HL #HT #L #H1 #L2 #H2 destruct
  elim (lfxs_inv_gref … H1) -H1 *
  [ #H1 #H0 destruct
    >(lfxs_inv_atom_sn … H2) -L2 //
  | #I1 #I #K1 #K #HK1 #H1 #H0 destruct
    elim (lfxs_inv_gref_bind_sn … H2) -H2 #I2 #K2 #HK2 #H destruct
    /4 width=3 by lfxs_gref, fqu_fqup/
  ]
| #p #I #V1 #T1 #HG #HL #HT #L #H1 #L2 #H2 destruct
  elim (lfxs_inv_bind … V1 V1 … H1) -H1 // #H1V #H1T
  elim (lfxs_inv_bind … V1 V1 … H2) -H2 // #H2V #H2T
  /3 width=4 by lfxs_bind/
| #I #V1 #T1 #HG #HL #HT #L #H1 #L2 #H2 destruct
  elim (lfxs_inv_flat … H1) -H1 #H1V #H1T
  elim (lfxs_inv_flat … H2) -H2 #H2V #H2T
  /3 width=3 by lfxs_flat/
]
qed-.

(* Negated inversion lemmas *************************************************)

(* Basic_2A1: uses: nllpx_sn_inv_bind nllpx_sn_inv_bind_O *)
lemma lfnxs_inv_bind: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                      ∀p,I,L1,L2,V,T. (L1 ⪤*[R, ⓑ{p,I}V.T] L2 → ⊥) →
                      (L1 ⪤*[R, V] L2 → ⊥) ∨ (L1.ⓑ{I}V ⪤*[R, T] L2.ⓑ{I}V → ⊥).
#R #HR #p #I #L1 #L2 #V #T #H elim (lfxs_dec … HR L1 L2 V)
/4 width=2 by lfxs_bind, or_intror, or_introl/
qed-.

(* Basic_2A1: uses: nllpx_sn_inv_flat *)
lemma lfnxs_inv_flat: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                      ∀I,L1,L2,V,T. (L1 ⪤*[R, ⓕ{I}V.T] L2 → ⊥) →
                      (L1 ⪤*[R, V] L2 → ⊥) ∨ (L1 ⪤*[R, T] L2 → ⊥).
#R #HR #I #L1 #L2 #V #T #H elim (lfxs_dec … HR L1 L2 V)
/4 width=1 by lfxs_flat, or_intror, or_introl/
qed-.

lemma lfnxs_inv_bind_void: ∀R. (∀L,T1,T2. Decidable (R L T1 T2)) →
                           ∀p,I,L1,L2,V,T. (L1 ⪤*[R, ⓑ{p,I}V.T] L2 → ⊥) →
                           (L1 ⪤*[R, V] L2 → ⊥) ∨ (L1.ⓧ ⪤*[R, T] L2.ⓧ → ⊥).
#R #HR #p #I #L1 #L2 #V #T #H elim (lfxs_dec … HR L1 L2 V)
/4 width=2 by lfxs_bind_void, or_intror, or_introl/
qed-.
