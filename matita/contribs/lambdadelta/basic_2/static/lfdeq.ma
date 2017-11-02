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

include "basic_2/notation/relations/lazyeqsn_5.ma".
include "basic_2/syntax/tdeq_ext.ma".
include "basic_2/static/lfxs.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

definition lfdeq: ∀h. sd h → relation3 term lenv lenv ≝
                  λh,o. lfxs (cdeq h o).

interpretation
   "degree-based equivalence on referred entries (local environment)"
   'LazyEqSn h o T L1 L2 = (lfdeq h o T L1 L2).

interpretation
   "degree-based ranged equivalence (local environment)"
   'LazyEqSn h o f L1 L2 = (lexs (cdeq_ext h o) cfull f L1 L2).
(*
definition lfdeq_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[h, o, T1] L2 → R L1 T1 T2.
*)
(* Basic properties ***********************************************************)

lemma frees_tdeq_conf_lexs: ∀h,o,f,L1,T1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f → ∀T2. T1 ≡[h, o] T2 →
                            ∀L2. L1 ≡[h, o, f] L2 → L2 ⊢ 𝐅*⦃T2⦄ ≡ f.
#h #o #f #L1 #T1 #H elim H -f -L1 -T1
[ #f #L1 #s1 #Hf #X #H1 #L2 #_
  elim (tdeq_inv_sort1 … H1) -H1 #s2 #d #_ #_ #H destruct
  /2 width=3 by frees_sort/
| #f #i #Hf #X #H1
  >(tdeq_inv_lref1 … H1) -X #Y #H2
  >(lexs_inv_atom1 … H2) -Y
  /2 width=1 by frees_atom/
| #f #I #L1 #V1 #_ #IH #X #H1
  >(tdeq_inv_lref1 … H1) -X #Y #H2
  elim (lexs_inv_next1 … H2) -H2 #Z #L2 #HL12 #HZ #H destruct
  elim (ext2_inv_pair_sn … HZ) -HZ #V2 #HV12 #H destruct
  /3 width=1 by frees_pair/
| #f #I #L1 #Hf #X #H1
  >(tdeq_inv_lref1 … H1) -X #Y #H2
  elim (lexs_inv_next1 … H2) -H2 #Z #L2 #_ #HZ #H destruct
  >(ext2_inv_unit_sn … HZ) -Z /2 width=1 by frees_unit/
| #f #I #L1 #i #_ #IH #X #H1
  >(tdeq_inv_lref1 … H1) -X #Y #H2
  elim (lexs_inv_push1 … H2) -H2 #J #L2 #HL12 #_ #H destruct
  /3 width=1 by frees_lref/
| #f #L1 #l #Hf #X #H1 #L2 #_
  >(tdeq_inv_gref1 … H1) -X /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (tdeq_inv_pair1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /6 width=5 by frees_bind, lexs_inv_tl, ext2_pair, sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (tdeq_inv_pair1 … H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /5 width=5 by frees_flat, sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn/
]
qed-.

lemma frees_tdeq_conf: ∀h,o,f,L,T1. L ⊢ 𝐅*⦃T1⦄ ≡ f →
                       ∀T2. T1 ≡[h, o] T2 → L ⊢ 𝐅*⦃T2⦄ ≡ f.
/4 width=7 by frees_tdeq_conf_lexs, lexs_refl, ext2_refl/ qed-.

lemma frees_lexs_conf: ∀h,o,f,L1,T. L1 ⊢ 𝐅*⦃T⦄ ≡ f →
                       ∀L2. L1 ≡[h, o, f] L2 → L2 ⊢ 𝐅*⦃T⦄ ≡ f.
/2 width=7 by frees_tdeq_conf_lexs, tdeq_refl/ qed-.

lemma frees_lfdeq_conf_lexs: ∀h,o. lexs_frees_confluent (cdeq_ext h o) cfull.
/3 width=7 by frees_tdeq_conf_lexs, ex2_intro/ qed-.

lemma tdeq_lfdeq_conf_sn: ∀h,o. s_r_confluent1 … (cdeq h o) (lfdeq h o).
#h #o #L1 #T1 #T2 #HT12 #L2 *
/3 width=5 by frees_tdeq_conf, ex2_intro/
qed-.

(* Basic_2A1: uses: lleq_sym *)
lemma lfdeq_sym: ∀h,o,T. symmetric … (lfdeq h o T).
#h #o #T #L1 #L2 *
/4 width=7 by frees_tdeq_conf_lexs, lfxs_sym, tdeq_sym, ex2_intro/
qed-.

lemma lfdeq_atom: ∀h,o,I. ⋆ ≡[h, o, ⓪{I}] ⋆.
/2 width=1 by lfxs_atom/ qed.

(* Basic_2A1: uses: lleq_sort *)
lemma lfdeq_sort: ∀h,o,I1,I2,L1,L2,s.
                  L1 ≡[h, o, ⋆s] L2 → L1.ⓘ{I1} ≡[h, o, ⋆s] L2.ⓘ{I2}.
/2 width=1 by lfxs_sort/ qed.

lemma lfdeq_pair: ∀h,o,I,L1,L2,V1,V2. L1 ≡[h, o, V1] L2 → V1 ≡[h, o] V2 →
                                      L1.ⓑ{I}V1 ≡[h, o, #0] L2.ⓑ{I}V2.
/2 width=1 by lfxs_pair/ qed.
(*
lemma lfdeq_unit: ∀h,o,f,I,L1,L2. 𝐈⦃f⦄ → L1 ⪤*[cdeq_ext h o, cfull, f] L2 →
                  L1.ⓤ{I} ≡[h, o, #0] L2.ⓤ{I}.
/2 width=3 by lfxs_unit/ qed.
*)
lemma lfdeq_lref: ∀h,o,I1,I2,L1,L2,i.
                  L1 ≡[h, o, #i] L2 → L1.ⓘ{I1} ≡[h, o, #⫯i] L2.ⓘ{I2}.
/2 width=1 by lfxs_lref/ qed.

(* Basic_2A1: uses: lleq_gref *)
lemma lfdeq_gref: ∀h,o,I1,I2,L1,L2,l.
                  L1 ≡[h, o, §l] L2 → L1.ⓘ{I1} ≡[h, o, §l] L2.ⓘ{I2}.
/2 width=1 by lfxs_gref/ qed.

lemma lfdeq_bind_repl_dx: ∀h,o,I,I1,L1,L2.∀T:term.
                          L1.ⓘ{I} ≡[h, o, T] L2.ⓘ{I1} →
                          ∀I2. I ≡[h, o] I2 →
                          L1.ⓘ{I} ≡[h, o, T] L2.ⓘ{I2}.
/2 width=2 by lfxs_bind_repl_dx/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma lfdeq_inv_atom_sn: ∀h,o,Y2. ∀T:term. ⋆ ≡[h, o, T] Y2 → Y2 = ⋆.
/2 width=3 by lfxs_inv_atom_sn/ qed-.

lemma lfdeq_inv_atom_dx: ∀h,o,Y1. ∀T:term. Y1 ≡[h, o, T] ⋆ → Y1 = ⋆.
/2 width=3 by lfxs_inv_atom_dx/ qed-.
(*
lemma lfdeq_inv_zero: ∀h,o,Y1,Y2. Y1 ≡[h, o, #0] Y2 →
                      ∨∨ Y1 = ⋆ ∧ Y2 = ⋆
                       | ∃∃I,L1,L2,V1,V2. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 &
                                          Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2
                       | ∃∃f,I,L1,L2. 𝐈⦃f⦄ & L1 ⪤*[cdeq_ext h o, cfull, f] L2 &
                                           Y1 = L1.ⓤ{I} & Y2 = L2.ⓤ{I}.
#h #o #Y1 #Y2 #H elim (lfxs_inv_zero … H) -H *
/3 width=9 by or3_intro0, or3_intro1, or3_intro2, ex4_5_intro, ex4_4_intro, conj/
qed-.
*)
lemma lfdeq_inv_lref: ∀h,o,Y1,Y2,i. Y1 ≡[h, o, #⫯i] Y2 →
                      (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                      ∃∃I1,I2,L1,L2. L1 ≡[h, o, #i] L2 &
                                     Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
/2 width=1 by lfxs_inv_lref/ qed-.

(* Basic_2A1: uses: lleq_inv_bind lleq_inv_bind_O *)
lemma lfdeq_inv_bind: ∀h,o,p,I,L1,L2,V,T. L1 ≡[h, o, ⓑ{p,I}V.T] L2 →
                      L1 ≡[h, o, V] L2 ∧ L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_inv_bind/ qed-.

(* Basic_2A1: uses: lleq_inv_flat *)
lemma lfdeq_inv_flat: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ⓕ{I}V.T] L2 →
                      L1 ≡[h, o, V] L2 ∧ L1 ≡[h, o, T] L2.
/2 width=2 by lfxs_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfdeq_inv_zero_pair_sn: ∀h,o,I,Y2,L1,V1. L1.ⓑ{I}V1 ≡[h, o, #0] Y2 →
                              ∃∃L2,V2. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 & Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_zero_pair_sn/ qed-.

lemma lfdeq_inv_zero_pair_dx: ∀h,o,I,Y1,L2,V2. Y1 ≡[h, o, #0] L2.ⓑ{I}V2 →
                              ∃∃L1,V1. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 & Y1 = L1.ⓑ{I}V1.
/2 width=1 by lfxs_inv_zero_pair_dx/ qed-.

lemma lfdeq_inv_lref_bind_sn: ∀h,o,I1,Y2,L1,i. L1.ⓘ{I1} ≡[h, o, #⫯i] Y2 →
                              ∃∃I2,L2. L1 ≡[h, o, #i] L2 & Y2 = L2.ⓘ{I2}.
/2 width=2 by lfxs_inv_lref_bind_sn/ qed-.

lemma lfdeq_inv_lref_bind_dx: ∀h,o,I2,Y1,L2,i. Y1 ≡[h, o, #⫯i] L2.ⓘ{I2} →
                              ∃∃I1,L1. L1 ≡[h, o, #i] L2 & Y1 = L1.ⓘ{I1}.
/2 width=2 by lfxs_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: uses: lleq_fwd_bind_sn lleq_fwd_flat_sn *)
lemma lfdeq_fwd_pair_sn: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ②{I}V.T] L2 → L1 ≡[h, o, V] L2.
/2 width=3 by lfxs_fwd_pair_sn/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_dx lleq_fwd_bind_O_dx *)
lemma lfdeq_fwd_bind_dx: ∀h,o,p,I,L1,L2,V,T.
                         L1 ≡[h, o, ⓑ{p,I}V.T] L2 → L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_fwd_bind_dx/ qed-.

(* Basic_2A1: uses: lleq_fwd_flat_dx *)
lemma lfdeq_fwd_flat_dx: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ⓕ{I}V.T] L2 → L1 ≡[h, o, T] L2.
/2 width=3 by lfxs_fwd_flat_dx/ qed-.

lemma lfdeq_fwd_dx: ∀h,o,I2,L1,K2. ∀T:term. L1 ≡[h, o, T] K2.ⓘ{I2} →
                    ∃∃I1,K1. L1 = K1.ⓘ{I1}.
/2 width=5 by lfxs_fwd_dx/ qed-.

(* Basic_2A1: removed theorems 10:
              lleq_ind lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_skip lleq_lref lleq_free
              lleq_Y lleq_ge_up lleq_ge
               
*)
