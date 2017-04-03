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

include "basic_2/notation/relations/lazyeq_5.ma".
include "basic_2/syntax/tdeq.ma".
include "basic_2/static/lfxs.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

definition lfdeq: ∀h. sd h → relation3 term lenv lenv ≝
                  λh,o. lfxs (cdeq h o).

interpretation
   "degree-based equivalence on referred entries (local environment)"
   'LazyEq h o T L1 L2 = (lfdeq h o T L1 L2).

interpretation
   "degree-based ranged equivalence (local environment)"
   'LazyEq h o f L1 L2 = (lexs (cdeq h o) cfull f L1 L2).
(*
definition lfdeq_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[h, o, T1] L2 → R L1 T1 T2.
*)
(* Basic properties ***********************************************************)

lemma frees_tdeq_conf_lexs: ∀h,o,f,L1,T1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f → ∀T2. T1 ≡[h, o] T2 →
                            ∀L2. L1 ≡[h, o, f] L2 → L2 ⊢ 𝐅*⦃T2⦄ ≡ f.
#h #o #f #L1 #T1 #H elim H -f -L1 -T1
[ #f #I1 #Hf #X #H1 elim (tdeq_fwd_atom1 … H1) -H1
  #I2 #H1 #Y #H2 lapply (lexs_inv_atom1 … H2) -H2
  #H2 destruct /2 width=1 by frees_atom/
| #f #I #L1 #V1 #s1 #_ #IH #X #H1 elim (tdeq_inv_sort1 … H1) -H1
  #s2 #d #Hs1 #Hs2 #H1 #Y #H2 elim (lexs_inv_push1 … H2) -H2
  #L2 #V2 #HL12 #_ #H2 destruct /4 width=3 by frees_sort, tdeq_sort/
| #f #I #L1 #V1 #_ #IH #X #H1 >(tdeq_inv_lref1 … H1) -H1
  #Y #H2 elim (lexs_inv_next1 … H2) -H2
  #L2 #V2 #HL12 #HV12 #H2 destruct /3 width=1 by frees_zero/
| #f #I #L1 #V1 #i #_ #IH #X #H1 >(tdeq_inv_lref1 … H1) -H1
  #Y #H2 elim (lexs_inv_push1 … H2) -H2
  #L2 #V2 #HL12 #_ #H2 destruct /3 width=1 by frees_lref/
| #f #I #L1 #V1 #l #_ #IH #X #H1 >(tdeq_inv_gref1 … H1) -H1
  #Y #H2 elim (lexs_inv_push1 … H2) -H2
  #L2 #V2 #HL12 #_ #H2 destruct /3 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /6 width=5 by frees_bind, lexs_inv_tl, sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /5 width=5 by frees_flat, sle_lexs_trans, sor_inv_sle_dx, sor_inv_sle_sn/
]
qed-.

lemma frees_tdeq_conf: ∀h,o,f,L,T1. L ⊢ 𝐅*⦃T1⦄ ≡ f →
                       ∀T2. T1 ≡[h, o] T2 → L ⊢ 𝐅*⦃T2⦄ ≡ f.
/3 width=7 by frees_tdeq_conf_lexs, lexs_refl/ qed-.

lemma frees_lfdeq_conf_lexs: ∀h,o. lexs_frees_confluent (cdeq h o) cfull.
/3 width=7 by frees_tdeq_conf_lexs, ex2_intro/ qed-.

lemma tdeq_lfdeq_conf_sn: ∀h,o. s_r_confluent1 … (cdeq h o) (lfdeq h o).
#h #o #L1 #T1 #T2 #HT12 #L2 *
/3 width=5 by frees_tdeq_conf, ex2_intro/
qed-.

lemma lfdeq_sym: ∀h,o,T. symmetric … (lfdeq h o T).
#h #o #T #L1 #L2 *
/4 width=7 by frees_tdeq_conf_lexs, lfxs_sym, tdeq_sym, ex2_intro/
qed-.

lemma lfdeq_atom: ∀h,o,I. ⋆ ≡[h, o, ⓪{I}] ⋆.
/2 width=1 by lfxs_atom/ qed.

lemma lfdeq_sort: ∀h,o,I,L1,L2,V1,V2,s.
                  L1 ≡[h, o, ⋆s] L2 → L1.ⓑ{I}V1 ≡[h, o, ⋆s] L2.ⓑ{I}V2.
/2 width=1 by lfxs_sort/ qed.

lemma lfdeq_zero: ∀h,o,I,L1,L2,V.
                  L1 ≡[h, o, V] L2 → L1.ⓑ{I}V ≡[h, o, #0] L2.ⓑ{I}V.
/2 width=1 by lfxs_zero/ qed.

lemma lfdeq_lref: ∀h,o,I,L1,L2,V1,V2,i.
                  L1 ≡[h, o, #i] L2 → L1.ⓑ{I}V1 ≡[h, o, #⫯i] L2.ⓑ{I}V2.
/2 width=1 by lfxs_lref/ qed.

lemma lfdeq_gref: ∀h,o,I,L1,L2,V1,V2,l.
                  L1 ≡[h, o, §l] L2 → L1.ⓑ{I}V1 ≡[h, o, §l] L2.ⓑ{I}V2.
/2 width=1 by lfxs_gref/ qed.

lemma lfdeq_pair_repl_dx: ∀h,o,I,L1,L2.∀T:term.∀V,V1.
                          L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V1 →
                          ∀V2. V ≡[h, o] V2 →
                          L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V2.
/2 width=2 by lfxs_pair_repl_dx/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma lfdeq_inv_atom_sn: ∀h,o,Y2. ∀T:term. ⋆ ≡[h, o, T] Y2 → Y2 = ⋆.
/2 width=3 by lfxs_inv_atom_sn/ qed-.

lemma lfdeq_inv_atom_dx: ∀h,o,Y1. ∀T:term. Y1 ≡[h, o, T] ⋆ → Y1 = ⋆.
/2 width=3 by lfxs_inv_atom_dx/ qed-.

lemma lfdeq_inv_zero: ∀h,o,Y1,Y2. Y1 ≡[h, o, #0] Y2 →
                      (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                      ∃∃I,L1,L2,V1,V2. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 &
                                       Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#h #o #Y1 #Y2 #H elim (lfxs_inv_zero … H) -H *
/3 width=9 by ex4_5_intro, or_introl, or_intror, conj/
qed-.

lemma lfdeq_inv_lref: ∀h,o,Y1,Y2,i. Y1 ≡[h, o, #⫯i] Y2 →
                      (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                      ∃∃I,L1,L2,V1,V2. L1 ≡[h, o, #i] L2 &
                                       Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
/2 width=1 by lfxs_inv_lref/ qed-.

lemma lfdeq_inv_bind: ∀h,o,p,I,L1,L2,V,T. L1 ≡[h, o, ⓑ{p,I}V.T] L2 →
                      L1 ≡[h, o, V] L2 ∧ L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_inv_bind/ qed-.

lemma lfdeq_inv_flat: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ⓕ{I}V.T] L2 →
                      L1 ≡[h, o, V] L2 ∧ L1 ≡[h, o, T] L2.
/2 width=2 by lfxs_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfdeq_inv_zero_pair_sn: ∀h,o,I,Y2,L1,V1. L1.ⓑ{I}V1 ≡[h, o, #0] Y2 →
                              ∃∃L2,V2. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 & Y2 = L2.ⓑ{I}V2.
#h #o #I #Y2 #L1 #V1 #H elim (lfxs_inv_zero_pair_sn … H) -H /2 width=5 by ex3_2_intro/
qed-.

lemma lfdeq_inv_zero_pair_dx: ∀h,o,I,Y1,L2,V2. Y1 ≡[h, o, #0] L2.ⓑ{I}V2 →
                              ∃∃L1,V1. L1 ≡[h, o, V1] L2 & V1 ≡[h, o] V2 & Y1 = L1.ⓑ{I}V1.
#h #o #I #Y1 #L2 #V2 #H elim (lfxs_inv_zero_pair_dx … H) -H
#L1 #V1 #HL12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma lfdeq_inv_lref_pair_sn: ∀h,o,I,Y2,L1,V1,i. L1.ⓑ{I}V1 ≡[h, o, #⫯i] Y2 →
                              ∃∃L2,V2. L1 ≡[h, o, #i] L2 & Y2 = L2.ⓑ{I}V2.
/2 width=2 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfdeq_inv_lref_pair_dx: ∀h,o,I,Y1,L2,V2,i. Y1 ≡[h, o, #⫯i] L2.ⓑ{I}V2 →
                              ∃∃L1,V1. L1 ≡[h, o, #i] L2 & Y1 = L1.ⓑ{I}V1.
/2 width=2 by lfxs_inv_lref_pair_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfdeq_fwd_bind_sn: ∀h,o,p,I,L1,L2,V,T. L1 ≡[h, o, ⓑ{p,I}V.T] L2 → L1 ≡[h, o, V] L2.
/2 width=4 by lfxs_fwd_bind_sn/ qed-.

lemma lfdeq_fwd_bind_dx: ∀h,o,p,I,L1,L2,V,T.
                         L1 ≡[h, o, ⓑ{p,I}V.T] L2 → L1.ⓑ{I}V ≡[h, o, T] L2.ⓑ{I}V.
/2 width=2 by lfxs_fwd_bind_dx/ qed-.

lemma lfdeq_fwd_flat_sn: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ⓕ{I}V.T] L2 → L1 ≡[h, o, V] L2.
/2 width=3 by lfxs_fwd_flat_sn/ qed-.

lemma lfdeq_fwd_flat_dx: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ⓕ{I}V.T] L2 → L1 ≡[h, o, T] L2.
/2 width=3 by lfxs_fwd_flat_dx/ qed-.

lemma lfdeq_fwd_pair_sn: ∀h,o,I,L1,L2,V,T. L1 ≡[h, o, ②{I}V.T] L2 → L1 ≡[h, o, V] L2.
/2 width=3 by lfxs_fwd_pair_sn/ qed-.

lemma lfdeq_fwd_dx: ∀h,o,I,L1,K2,V2. ∀T:term. L1 ≡[h, o, T] K2.ⓑ{I}V2 →
                    ∃∃K1,V1. L1 = K1.ⓑ{I}V1.
/2 width=5 by lfxs_fwd_dx/ qed-.

(* Basic_2A1: removed theorems 30: 
              lleq_ind lleq_inv_bind lleq_inv_flat lleq_fwd_length lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_fwd_bind_sn lleq_fwd_bind_dx lleq_fwd_flat_sn lleq_fwd_flat_dx
              lleq_sort lleq_skip lleq_lref lleq_free lleq_gref lleq_bind lleq_flat
              lleq_refl lleq_Y lleq_sym lleq_ge_up lleq_ge lleq_bind_O llpx_sn_lrefl
              lleq_trans lleq_canc_sn lleq_canc_dx lleq_nlleq_trans nlleq_lleq_div
*)
