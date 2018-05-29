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
include "basic_2/syntax/cext2.ma".
include "basic_2/relocation/lexs.ma".
include "basic_2/static/frees.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition lfxs (R) (T): relation lenv ≝
                λL1,L2. ∃∃f. L1 ⊢ 𝐅*⦃T⦄ ≘ f & L1 ⪤*[cext2 R, cfull, f] L2.

interpretation "generic extension on referred entries (local environment)"
   'RelationStar R T L1 L2 = (lfxs R T L1 L2).

definition R_confluent2_lfxs: relation4 (relation3 lenv term term)
                                        (relation3 lenv term term) … ≝
                              λR1,R2,RP1,RP2.
                              ∀L0,T0,T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                              ∀L1. L0 ⪤*[RP1, T0] L1 → ∀L2. L0 ⪤*[RP2, T0] L2 →
                              ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

definition lfxs_confluent: relation … ≝
                           λR1,R2. 
                           ∀K1,K,V1. K1 ⪤*[R1, V1] K → ∀V. R1 K1 V1 V →
                           ∀K2. K ⪤*[R2, V] K2 → K ⪤*[R2, V1] K2.

definition lfxs_transitive: relation3 ? (relation3 ?? term) … ≝
                            λR1,R2,R3.
                            ∀K1,K,V1. K1 ⪤*[R1, V1] K →
                            ∀V. R1 K1 V1 V → ∀V2. R2 K V V2 → R3 K1 V1 V2.

(* Basic inversion lemmas ***************************************************)

lemma lfxs_inv_atom_sn (R): ∀Y2,T. ⋆ ⪤*[R, T] Y2 → Y2 = ⋆.
#R #Y2 #T * /2 width=4 by lexs_inv_atom1/
qed-.

lemma lfxs_inv_atom_dx (R): ∀Y1,T. Y1 ⪤*[R, T] ⋆ → Y1 = ⋆.
#R #I #Y1 * /2 width=4 by lexs_inv_atom2/
qed-.

lemma lfxs_inv_sort (R): ∀Y1,Y2,s. Y1 ⪤*[R, ⋆s] Y2 →
                         ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                          | ∃∃I1,I2,L1,L2. L1 ⪤*[R, ⋆s] L2 &
                                           Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
#R * [ | #Y1 #I1 ] #Y2 #s * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or_introl, conj/
| lapply (frees_inv_sort … H1) -H1 #Hf
  elim (isid_inv_gen … Hf) -Hf #g #Hg #H destruct
  elim (lexs_inv_push1 … H2) -H2 #I2 #L2 #H12 #_ #H destruct
  /5 width=7 by frees_sort, ex3_4_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_zero (R): ∀Y1,Y2. Y1 ⪤*[R, #0] Y2 →
                         ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                          | ∃∃I,L1,L2,V1,V2. L1 ⪤*[R, V1] L2 & R L1 V1 V2 &
                                             Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2
                          | ∃∃f,I,L1,L2. 𝐈⦃f⦄ & L1 ⪤*[cext2 R, cfull, f] L2 &
                                         Y1 = L1.ⓤ{I} & Y2 = L2.ⓤ{I}.
#R * [ | #Y1 * #I1 [ | #X ] ] #Y2 * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or3_intro0, conj/
| elim (frees_inv_unit … H1) -H1 #g #HX #H destruct
  elim (lexs_inv_next1 … H2) -H2 #I2 #L2 #HL12 #H #H2 destruct
  >(ext2_inv_unit_sn … H) -H /3 width=8 by or3_intro2, ex4_4_intro/
| elim (frees_inv_pair … H1) -H1 #g #Hg #H destruct
  elim (lexs_inv_next1 … H2) -H2 #Z2 #L2 #HL12 #H
  elim (ext2_inv_pair_sn … H) -H
  /4 width=9 by or3_intro1, ex4_5_intro, ex2_intro/
]
qed-.

lemma lfxs_inv_lref (R): ∀Y1,Y2,i. Y1 ⪤*[R, #↑i] Y2 →
                         ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                          | ∃∃I1,I2,L1,L2. L1 ⪤*[R, #i] L2 &
                                           Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
#R * [ | #Y1 #I1 ] #Y2 #i * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or_introl, conj/
| elim (frees_inv_lref … H1) -H1 #g #Hg #H destruct
  elim (lexs_inv_push1 … H2) -H2
  /4 width=7 by ex3_4_intro, ex2_intro, or_intror/
]
qed-.

lemma lfxs_inv_gref (R): ∀Y1,Y2,l. Y1 ⪤*[R, §l] Y2 →
                         ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                          | ∃∃I1,I2,L1,L2. L1 ⪤*[R, §l] L2 &
                                           Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
#R * [ | #Y1 #I1 ] #Y2 #l * #f #H1 #H2
[ lapply (lexs_inv_atom1 … H2) -H2 /3 width=1 by or_introl, conj/
| lapply (frees_inv_gref … H1) -H1 #Hf
  elim (isid_inv_gen … Hf) -Hf #g #Hg #H destruct
  elim (lexs_inv_push1 … H2) -H2 #I2 #L2 #H12 #_ #H destruct
  /5 width=7 by frees_gref, ex3_4_intro, ex2_intro, or_intror/
]
qed-.

(* Basic_2A1: uses: llpx_sn_inv_bind llpx_sn_inv_bind_O *)
lemma lfxs_inv_bind (R): ∀p,I,L1,L2,V1,V2,T. L1 ⪤*[R, ⓑ{p,I}V1.T] L2 → R L1 V1 V2 →
                         ∧∧ L1 ⪤*[R, V1] L2 & L1.ⓑ{I}V1 ⪤*[R, T] L2.ⓑ{I}V2.
#R #p #I #L1 #L2 #V1 #V2 #T * #f #Hf #HL #HV elim (frees_inv_bind … Hf) -Hf
/6 width=6 by sle_lexs_trans, lexs_inv_tl, ext2_pair, sor_inv_sle_dx, sor_inv_sle_sn, ex2_intro, conj/
qed-.

(* Basic_2A1: uses: llpx_sn_inv_flat *)
lemma lfxs_inv_flat (R): ∀I,L1,L2,V,T. L1 ⪤*[R, ⓕ{I}V.T] L2 →
                         ∧∧ L1 ⪤*[R, V] L2 & L1 ⪤*[R, T] L2.
#R #I #L1 #L2 #V #T * #f #Hf #HL elim (frees_inv_flat … Hf) -Hf
/5 width=6 by sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn, ex2_intro, conj/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfxs_inv_sort_bind_sn (R): ∀I1,K1,L2,s. K1.ⓘ{I1} ⪤*[R, ⋆s] L2 →
                                 ∃∃I2,K2. K1 ⪤*[R, ⋆s] K2 & L2 = K2.ⓘ{I2}.
#R #I1 #K1 #L2 #s #H elim (lfxs_inv_sort … H) -H *
[ #H destruct
| #Z1 #I2 #Y1 #K2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_sort_bind_dx (R): ∀I2,K2,L1,s. L1 ⪤*[R, ⋆s] K2.ⓘ{I2} →
                                 ∃∃I1,K1. K1 ⪤*[R, ⋆s] K2 & L1 = K1.ⓘ{I1}.
#R #I2 #K2 #L1 #s #H elim (lfxs_inv_sort … H) -H *
[ #_ #H destruct
| #I1 #Z2 #K1 #Y2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_zero_pair_sn (R): ∀I,L2,K1,V1. K1.ⓑ{I}V1 ⪤*[R, #0] L2 →
                                 ∃∃K2,V2. K1 ⪤*[R, V1] K2 & R K1 V1 V2 &
                                          L2 = K2.ⓑ{I}V2.
#R #I #L2 #K1 #V1 #H elim (lfxs_inv_zero … H) -H *
[ #H destruct
| #Z #Y1 #K2 #X1 #V2 #HK12 #HV12 #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
| #f #Z #Y1 #Y2 #_ #_ #H destruct
]
qed-.

lemma lfxs_inv_zero_pair_dx (R): ∀I,L1,K2,V2. L1 ⪤*[R, #0] K2.ⓑ{I}V2 →
                                 ∃∃K1,V1. K1 ⪤*[R, V1] K2 & R K1 V1 V2 &
                                          L1 = K1.ⓑ{I}V1.
#R #I #L1 #K2 #V2 #H elim (lfxs_inv_zero … H) -H *
[ #_ #H destruct
| #Z #K1 #Y2 #V1 #X2 #HK12 #HV12 #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
| #f #Z #Y1 #Y2 #_ #_ #_ #H destruct
]
qed-.

lemma lfxs_inv_zero_unit_sn (R): ∀I,K1,L2. K1.ⓤ{I} ⪤*[R, #0] L2 →
                                 ∃∃f,K2. 𝐈⦃f⦄ & K1 ⪤*[cext2 R, cfull, f] K2 &
                                         L2 = K2.ⓤ{I}.
#R #I #K1 #L2 #H elim (lfxs_inv_zero … H) -H *
[ #H destruct
| #Z #Y1 #Y2 #X1 #X2 #_ #_ #H destruct
| #f #Z #Y1 #K2 #Hf #HK12 #H1 #H2 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lfxs_inv_zero_unit_dx (R): ∀I,L1,K2. L1 ⪤*[R, #0] K2.ⓤ{I} →
                                 ∃∃f,K1. 𝐈⦃f⦄ & K1 ⪤*[cext2 R, cfull, f] K2 &
                                         L1 = K1.ⓤ{I}.
#R #I #L1 #K2 #H elim (lfxs_inv_zero … H) -H *
[ #_ #H destruct
| #Z #Y1 #Y2 #X1 #X2 #_ #_ #_ #H destruct
| #f #Z #K1 #Y2 #Hf #HK12 #H1 #H2 destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lfxs_inv_lref_bind_sn (R): ∀I1,K1,L2,i. K1.ⓘ{I1} ⪤*[R, #↑i] L2 →
                                 ∃∃I2,K2. K1 ⪤*[R, #i] K2 & L2 = K2.ⓘ{I2}.
#R #I1 #K1 #L2 #i #H elim (lfxs_inv_lref … H) -H *
[ #H destruct
| #Z1 #I2 #Y1 #K2 #Hi #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_lref_bind_dx (R): ∀I2,K2,L1,i. L1 ⪤*[R, #↑i] K2.ⓘ{I2} →
                                 ∃∃I1,K1. K1 ⪤*[R, #i] K2 & L1 = K1.ⓘ{I1}.
#R #I2 #K2 #L1 #i #H elim (lfxs_inv_lref … H) -H *
[ #_ #H destruct
| #I1 #Z2 #K1 #Y2 #Hi #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_gref_bind_sn (R): ∀I1,K1,L2,l. K1.ⓘ{I1} ⪤*[R, §l] L2 →
                                 ∃∃I2,K2. K1 ⪤*[R, §l] K2 & L2 = K2.ⓘ{I2}.
#R #I1 #K1 #L2 #l #H elim (lfxs_inv_gref … H) -H *
[ #H destruct
| #Z1 #I2 #Y1 #K2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma lfxs_inv_gref_bind_dx (R): ∀I2,K2,L1,l. L1 ⪤*[R, §l] K2.ⓘ{I2} →
                                 ∃∃I1,K1. K1 ⪤*[R, §l] K2 & L1 = K1.ⓘ{I1}.
#R #I2 #K2 #L1 #l #H elim (lfxs_inv_gref … H) -H *
[ #_ #H destruct
| #I1 #Z2 #K1 #Y2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lfxs_fwd_zero_pair (R): ∀I,K1,K2,V1,V2.
                              K1.ⓑ{I}V1 ⪤*[R, #0] K2.ⓑ{I}V2 → K1 ⪤*[R, V1] K2.
#R #I #K1 #K2 #V1 #V2 #H
elim (lfxs_inv_zero_pair_sn … H) -H #Y #X #HK12 #_ #H destruct //
qed-.

(* Basic_2A1: uses: llpx_sn_fwd_pair_sn llpx_sn_fwd_bind_sn llpx_sn_fwd_flat_sn *)
lemma lfxs_fwd_pair_sn (R): ∀I,L1,L2,V,T. L1 ⪤*[R, ②{I}V.T] L2 → L1 ⪤*[R, V] L2.
#R * [ #p ] #I #L1 #L2 #V #T * #f #Hf #HL
[ elim (frees_inv_bind … Hf) | elim (frees_inv_flat … Hf) ] -Hf
/4 width=6 by sle_lexs_trans, sor_inv_sle_sn, ex2_intro/
qed-.

(* Basic_2A1: uses: llpx_sn_fwd_bind_dx llpx_sn_fwd_bind_O_dx *)
lemma lfxs_fwd_bind_dx (R): ∀p,I,L1,L2,V1,V2,T. L1 ⪤*[R, ⓑ{p,I}V1.T] L2 →
                            R L1 V1 V2 → L1.ⓑ{I}V1 ⪤*[R, T] L2.ⓑ{I}V2.
#R #p #I #L1 #L2 #V1 #V2 #T #H #HV elim (lfxs_inv_bind … H HV) -H -HV //
qed-.

(* Basic_2A1: uses: llpx_sn_fwd_flat_dx *)
lemma lfxs_fwd_flat_dx (R): ∀I,L1,L2,V,T. L1 ⪤*[R, ⓕ{I}V.T] L2 → L1 ⪤*[R, T] L2.
#R #I #L1 #L2 #V #T #H elim (lfxs_inv_flat … H) -H //
qed-.

lemma lfxs_fwd_dx (R): ∀I2,L1,K2,T. L1 ⪤*[R, T] K2.ⓘ{I2} →
                       ∃∃I1,K1. L1 = K1.ⓘ{I1}.
#R #I2 #L1 #K2 #T * #f elim (pn_split f) * #g #Hg #_ #Hf destruct
[ elim (lexs_inv_push2 … Hf) | elim (lexs_inv_next2 … Hf) ] -Hf #I1 #K1 #_ #_ #H destruct
/2 width=3 by ex1_2_intro/
qed-.

(* Basic properties *********************************************************)

lemma lfxs_atom (R): ∀I. ⋆ ⪤*[R, ⓪{I}] ⋆.
#R * /3 width=3 by frees_sort, frees_atom, frees_gref, lexs_atom, ex2_intro/
qed.

lemma lfxs_sort (R): ∀I1,I2,L1,L2,s.
                     L1 ⪤*[R, ⋆s] L2 → L1.ⓘ{I1} ⪤*[R, ⋆s] L2.ⓘ{I2}.
#R #I1 #I2 #L1 #L2 #s * #f #Hf #H12
lapply (frees_inv_sort … Hf) -Hf
/4 width=3 by frees_sort, lexs_push, isid_push, ex2_intro/
qed.

lemma lfxs_pair (R): ∀I,L1,L2,V1,V2. L1 ⪤*[R, V1] L2 →
                     R L1 V1 V2 → L1.ⓑ{I}V1 ⪤*[R, #0] L2.ⓑ{I}V2.
#R #I1 #I2 #L1 #L2 #V1 *
/4 width=3 by ext2_pair, frees_pair, lexs_next, ex2_intro/
qed.

lemma lfxs_unit (R): ∀f,I,L1,L2. 𝐈⦃f⦄ → L1 ⪤*[cext2 R, cfull, f] L2 →
                     L1.ⓤ{I} ⪤*[R, #0] L2.ⓤ{I}.
/4 width=3 by frees_unit, lexs_next, ext2_unit, ex2_intro/ qed.

lemma lfxs_lref (R): ∀I1,I2,L1,L2,i.
                 L1 ⪤*[R, #i] L2 → L1.ⓘ{I1} ⪤*[R, #↑i] L2.ⓘ{I2}.
#R #I1 #I2 #L1 #L2 #i * /3 width=3 by lexs_push, frees_lref, ex2_intro/
qed.

lemma lfxs_gref (R): ∀I1,I2,L1,L2,l.
                     L1 ⪤*[R, §l] L2 → L1.ⓘ{I1} ⪤*[R, §l] L2.ⓘ{I2}.
#R #I1 #I2 #L1 #L2 #l * #f #Hf #H12
lapply (frees_inv_gref … Hf) -Hf
/4 width=3 by frees_gref, lexs_push, isid_push, ex2_intro/
qed.

lemma lfxs_bind_repl_dx (R): ∀I,I1,L1,L2,T.
                             L1.ⓘ{I} ⪤*[R, T] L2.ⓘ{I1} →
                             ∀I2. cext2 R L1 I I2 →
                             L1.ⓘ{I} ⪤*[R, T] L2.ⓘ{I2}.
#R #I #I1 #L1 #L2 #T * #f #Hf #HL12 #I2 #HR
/3 width=5 by lexs_pair_repl, ex2_intro/
qed-.

(* Basic_2A1: uses: llpx_sn_co *)
lemma lfxs_co (R1) (R2): (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
                         ∀L1,L2,T. L1 ⪤*[R1, T] L2 → L1 ⪤*[R2, T] L2.
#R1 #R2 #HR #L1 #L2 #T * /5 width=7 by lexs_co, cext2_co, ex2_intro/
qed-.

lemma lfxs_isid (R1) (R2): ∀L1,L2,T1,T2.
                           (∀f. L1 ⊢ 𝐅*⦃T1⦄ ≘ f → 𝐈⦃f⦄) →
                           (∀f. 𝐈⦃f⦄ → L1 ⊢ 𝐅*⦃T2⦄ ≘ f) →
                           L1 ⪤*[R1, T1] L2 → L1 ⪤*[R2, T2] L2.
#R1 #R2 #L1 #L2 #T1 #T2 #H1 #H2 *
/4 width=7 by lexs_co_isid, ex2_intro/
qed-.

lemma lfxs_unit_sn (R1) (R2): 
                   ∀I,K1,L2. K1.ⓤ{I} ⪤*[R1, #0] L2 → K1.ⓤ{I} ⪤*[R2, #0] L2.
#R1 #R2 #I #K1 #L2 #H
elim (lfxs_inv_zero_unit_sn … H) -H #f #K2 #Hf #HK12 #H destruct
/3 width=7 by lfxs_unit, lexs_co_isid/
qed-.

(* Basic_2A1: removed theorems 9:
              llpx_sn_skip llpx_sn_lref llpx_sn_free 
              llpx_sn_fwd_lref
              llpx_sn_Y llpx_sn_ge_up llpx_sn_ge 
              llpx_sn_fwd_drop_sn llpx_sn_fwd_drop_dx      
*)
