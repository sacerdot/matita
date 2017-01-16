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

include "ground_2/relocation/rtmap_id.ma".
include "basic_2/notation/relations/relationstar_4.ma".
include "basic_2/grammar/ceq.ma".
include "basic_2/relocation/lexs.ma".
include "basic_2/static/frees.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition lfxs (R) (T): relation lenv ≝
                λL1,L2. ∃∃f. L1 ⊢ 𝐅*⦃T⦄ ≡ f & L1 ⦻*[R, cfull, f] L2.

interpretation "generic extension on referred entries (local environment)"
   'RelationStar R T L1 L2 = (lfxs R T L1 L2).

definition R_frees_confluent: predicate (relation3 lenv term term) ≝
                              λRN.
                              ∀f1,L,T1. L ⊢ 𝐅*⦃T1⦄ ≡ f1 → ∀T2. RN L T1 T2 →
                              ∃∃f2. L ⊢ 𝐅*⦃T2⦄ ≡ f2 & f2 ⊆ f1.

definition lexs_frees_confluent: relation (relation3 lenv term term) ≝
                                 λRN,RP.
                                 ∀f1,L1,T. L1 ⊢ 𝐅*⦃T⦄ ≡ f1 →
                                 ∀L2. L1 ⦻*[RN, RP, f1] L2 →
                                 ∃∃f2. L2 ⊢ 𝐅*⦃T⦄ ≡ f2 & f2 ⊆ f1.

definition R_confluent2_lfxs: relation4 (relation3 lenv term term)
                                        (relation3 lenv term term) … ≝
                              λR1,R2,RP1,RP2.
                              ∀L0,T0,T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                              ∀L1. L0 ⦻*[RP1, T0] L1 → ∀L2. L0 ⦻*[RP2, T0] L2 →
                              ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

(* Basic properties ***********************************************************)

lemma lfxs_atom: ∀R,I. ⋆ ⦻*[R, ⓪{I}] ⋆.
/3 width=3 by lexs_atom, frees_atom, ex2_intro/
qed.

lemma lfxs_sort: ∀R,I,L1,L2,V1,V2,s.
                 L1 ⦻*[R, ⋆s] L2 → L1.ⓑ{I}V1 ⦻*[R, ⋆s] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #s * /3 width=3 by lexs_push, frees_sort, ex2_intro/
qed.

lemma lfxs_zero: ∀R,I,L1,L2,V1,V2. L1 ⦻*[R, V1] L2 →
                 R L1 V1 V2 → L1.ⓑ{I}V1 ⦻*[R, #0] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 * /3 width=3 by lexs_next, frees_zero, ex2_intro/
qed.

lemma lfxs_lref: ∀R,I,L1,L2,V1,V2,i.
                 L1 ⦻*[R, #i] L2 → L1.ⓑ{I}V1 ⦻*[R, #⫯i] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #i * /3 width=3 by lexs_push, frees_lref, ex2_intro/
qed.

lemma lfxs_gref: ∀R,I,L1,L2,V1,V2,l.
                 L1 ⦻*[R, §l] L2 → L1.ⓑ{I}V1 ⦻*[R, §l] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #l * /3 width=3 by lexs_push, frees_gref, ex2_intro/
qed.

lemma lfxs_pair_repl_dx: ∀R,I,L1,L2,T,V,V1.
                         L1.ⓑ{I}V ⦻*[R, T] L2.ⓑ{I}V1 →
                         ∀V2. R L1 V V2 →
                         L1.ⓑ{I}V ⦻*[R, T] L2.ⓑ{I}V2.
#R #I #L1 #L2 #T #V #V1 * #f #Hf #HL12 #V2 #HR
/3 width=5 by lexs_pair_repl, ex2_intro/
qed-.

lemma lfxs_co: ∀R1,R2. (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
               ∀L1,L2,T. L1 ⦻*[R1, T] L2 → L1 ⦻*[R2, T] L2.
#R1 #R2 #HR #L1 #L2 #T * /4 width=7 by lexs_co, ex2_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma lfxs_inv_atom_sn: ∀R,I,Y2. ⋆ ⦻*[R, ⓪{I}] Y2 → Y2 = ⋆.
#R #I #Y2 * /2 width=4 by lexs_inv_atom1/
qed-.

lemma lfxs_inv_atom_dx: ∀R,I,Y1. Y1 ⦻*[R, ⓪{I}] ⋆ → Y1 = ⋆.
#R #I #Y1 * /2 width=4 by lexs_inv_atom2/
qed-.

lemma lfxs_inv_sort: ∀R,Y1,Y2,s. Y1 ⦻*[R, ⋆s] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V1,V2. L1 ⦻*[R, ⋆s] L2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R * [ | #Y1 #I #V1 ] #Y2 #s * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or_introl, conj/
| lapply (frees_inv_sort … H1) -H1 #Hf
  elim (isid_inv_gen … Hf) -Hf #g #Hg #H destruct
  elim (lexs_inv_push1 … H2) -H2 #L2 #V2 #H12 #_ #H destruct
  /5 width=8 by frees_sort_gen, ex3_5_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_zero: ∀R,Y1,Y2. Y1 ⦻*[R, #0] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V1,V2. L1 ⦻*[R, V1] L2 & R L1 V1 V2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R #Y1 #Y2 * #f #H1 #H2 elim (frees_inv_zero … H1) -H1 *
[ #H #_ lapply (lexs_inv_atom1_aux … H2 H) -H2 /3 width=1 by or_introl, conj/
| #I1 #L1 #V1 #g #HV1 #HY1 #Hg elim (lexs_inv_next1_aux … H2 … HY1 Hg) -H2 -Hg
  /4 width=9 by ex4_5_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_lref: ∀R,Y1,Y2,i. Y1 ⦻*[R, #⫯i] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V1,V2. L1 ⦻*[R, #i] L2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R #Y1 #Y2 #i * #f #H1 #H2 elim (frees_inv_lref … H1) -H1 *
[ #H #_ lapply (lexs_inv_atom1_aux … H2 H) -H2 /3 width=1 by or_introl, conj/
| #I1 #L1 #V1 #g #HV1 #HY1 #Hg elim (lexs_inv_push1_aux … H2 … HY1 Hg) -H2 -Hg
  /4 width=8 by ex3_5_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_gref: ∀R,Y1,Y2,l. Y1 ⦻*[R, §l] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V1,V2. L1 ⦻*[R, §l] L2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R * [ | #Y1 #I #V1 ] #Y2 #l * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or_introl, conj/
| lapply (frees_inv_gref … H1) -H1 #Hf
  elim (isid_inv_gen … Hf) -Hf #g #Hg #H destruct
  elim (lexs_inv_push1 … H2) -H2 #L2 #V2 #H12 #_ #H destruct
  /5 width=8 by frees_gref_gen, ex3_5_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_bind: ∀R,p,I,L1,L2,V1,V2,T. L1 ⦻*[R, ⓑ{p,I}V1.T] L2 → R L1 V1 V2 →
                     L1 ⦻*[R, V1] L2 ∧ L1.ⓑ{I}V1 ⦻*[R, T] L2.ⓑ{I}V2.
#R #p #I #L1 #L2 #V1 #V2 #T * #f #Hf #HL #HV elim (frees_inv_bind … Hf) -Hf
/6 width=6 by sle_lexs_trans, lexs_inv_tl, sor_inv_sle_dx, sor_inv_sle_sn, ex2_intro, conj/
qed-.

lemma lfxs_inv_flat: ∀R,I,L1,L2,V,T. L1 ⦻*[R, ⓕ{I}V.T] L2 →
                     L1 ⦻*[R, V] L2 ∧ L1 ⦻*[R, T] L2.
#R #I #L1 #L2 #V #T * #f #Hf #HL elim (frees_inv_flat … Hf) -Hf
/5 width=6 by sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn, ex2_intro, conj/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfxs_inv_sort_pair_sn: ∀R,I,Y2,L1,V1,s. L1.ⓑ{I}V1 ⦻*[R, ⋆s] Y2 →
                             ∃∃L2,V2. L1 ⦻*[R, ⋆s] L2 & Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #s #H elim (lfxs_inv_sort … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_sort_pair_dx: ∀R,I,Y1,L2,V2,s. Y1 ⦻*[R, ⋆s] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. L1 ⦻*[R, ⋆s] L2 & Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #s #H elim (lfxs_inv_sort … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_zero_pair_sn: ∀R,I,Y2,L1,V1. L1.ⓑ{I}V1 ⦻*[R, #0] Y2 →
                             ∃∃L2,V2. L1 ⦻*[R, V1] L2 & R L1 V1 V2 &
                                      Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #H elim (lfxs_inv_zero … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #HV1 #HV12 #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lfxs_inv_zero_pair_dx: ∀R,I,Y1,L2,V2. Y1 ⦻*[R, #0] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. L1 ⦻*[R, V1] L2 & R L1 V1 V2 &
                                      Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #H elim (lfxs_inv_zero … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #HV1 #HV12 #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lfxs_inv_lref_pair_sn: ∀R,I,Y2,L1,V1,i. L1.ⓑ{I}V1 ⦻*[R, #⫯i] Y2 →
                             ∃∃L2,V2. L1 ⦻*[R, #i] L2 & Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #i #H elim (lfxs_inv_lref … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #Hi #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_lref_pair_dx: ∀R,I,Y1,L2,V2,i. Y1 ⦻*[R, #⫯i] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. L1 ⦻*[R, #i] L2 & Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #i #H elim (lfxs_inv_lref … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #Hi #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_gref_pair_sn: ∀R,I,Y2,L1,V1,l. L1.ⓑ{I}V1 ⦻*[R, §l] Y2 →
                             ∃∃L2,V2. L1 ⦻*[R, §l] L2 & Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #l #H elim (lfxs_inv_gref … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_gref_pair_dx: ∀R,I,Y1,L2,V2,l. Y1 ⦻*[R, §l] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. L1 ⦻*[R, §l] L2 & Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #l #H elim (lfxs_inv_gref … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lfxs_fwd_bind_sn: ∀R,p,I,L1,L2,V,T. L1 ⦻*[R, ⓑ{p,I}V.T] L2 → L1 ⦻*[R, V] L2.
#R #p #I #L1 #L2 #V #T * #f #Hf #HL elim (frees_inv_bind … Hf) -Hf
/4 width=6 by sle_lexs_trans, sor_inv_sle_sn, ex2_intro/
qed-.

lemma lfxs_fwd_bind_dx: ∀R,p,I,L1,L2,V1,V2,T. L1 ⦻*[R, ⓑ{p,I}V1.T] L2 →
                        R L1 V1 V2 → L1.ⓑ{I}V1 ⦻*[R, T] L2.ⓑ{I}V2.
#R #p #I #L1 #L2 #V1 #V2 #T #H #HV elim (lfxs_inv_bind … H HV) -H -HV //
qed-.

lemma lfxs_fwd_flat_sn: ∀R,I,L1,L2,V,T. L1 ⦻*[R, ⓕ{I}V.T] L2 → L1 ⦻*[R, V] L2.
#R #I #L1 #L2 #V #T #H elim (lfxs_inv_flat … H) -H //
qed-.

lemma lfxs_fwd_flat_dx: ∀R,I,L1,L2,V,T. L1 ⦻*[R, ⓕ{I}V.T] L2 → L1 ⦻*[R, T] L2.
#R #I #L1 #L2 #V #T #H elim (lfxs_inv_flat … H) -H //
qed-.

lemma lfxs_fwd_pair_sn: ∀R,I,L1,L2,V,T. L1 ⦻*[R, ②{I}V.T] L2 → L1 ⦻*[R, V] L2.
#R * /2 width=4 by lfxs_fwd_flat_sn, lfxs_fwd_bind_sn/
qed-.

(* Basic_2A1: removed theorems 24:
              llpx_sn_sort llpx_sn_skip llpx_sn_lref llpx_sn_free llpx_sn_gref
              llpx_sn_bind llpx_sn_flat
              llpx_sn_inv_bind llpx_sn_inv_flat
              llpx_sn_fwd_lref llpx_sn_fwd_pair_sn llpx_sn_fwd_length
              llpx_sn_fwd_bind_sn llpx_sn_fwd_bind_dx llpx_sn_fwd_flat_sn llpx_sn_fwd_flat_dx
              llpx_sn_refl llpx_sn_Y llpx_sn_bind_O llpx_sn_ge_up llpx_sn_ge llpx_sn_co
              llpx_sn_fwd_drop_sn llpx_sn_fwd_drop_dx              
*)
