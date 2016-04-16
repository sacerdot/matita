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

include "basic_2/notation/relations/lazyeq_3.ma".
include "basic_2/static/lfxs.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *******************)

definition lfeq: relation3 term lenv lenv ≝ lfxs ceq.

interpretation
   "equivalence on referred entries (local environment)"
   'LazyEq T L1 L2 = (lfeq T L1 L2).

definition lfeq_transitive: predicate (relation3 lenv term term) ≝
           λR. ∀L2,T1,T2. R L2 T1 T2 → ∀L1. L1 ≡[T1] L2 → R L1 T1 T2.

(* Basic properties ***********************************************************)

lemma lfeq_atom: ∀I. ⋆ ≡[⓪{I}] ⋆.
/2 width=1 by lfxs_atom/ qed.

lemma lfeq_sort: ∀I,L1,L2,V1,V2,s.
                 L1 ≡[⋆s] L2 → L1.ⓑ{I}V1 ≡[⋆s] L2.ⓑ{I}V2.
/2 width=1 by lfxs_sort/ qed.

lemma lfeq_zero: ∀I,L1,L2,V.
                 L1 ≡[V] L2 → L1.ⓑ{I}V ≡[#0] L2.ⓑ{I}V.
/2 width=1 by lfxs_zero/ qed.

lemma lfeq_lref: ∀I,L1,L2,V1,V2,i.
                 L1 ≡[#i] L2 → L1.ⓑ{I}V1 ≡[#⫯i] L2.ⓑ{I}V2.
/2 width=1 by lfxs_lref/ qed.

lemma lfeq_gref: ∀I,L1,L2,V1,V2,l.
                 L1 ≡[§l] L2 → L1.ⓑ{I}V1 ≡[§l] L2.ⓑ{I}V2.
/2 width=1 by lfxs_gref/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lfeq_inv_atom_sn: ∀I,Y2. ⋆ ≡[⓪{I}] Y2 → Y2 = ⋆.
/2 width=3 by lfxs_inv_atom_sn/ qed-.

lemma lfeq_inv_atom_dx: ∀I,Y1. Y1 ≡[⓪{I}] ⋆ → Y1 = ⋆.
/2 width=3 by lfxs_inv_atom_dx/ qed-.

lemma lfeq_inv_zero: ∀Y1,Y2. Y1 ≡[#0] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V. L1 ≡[V] L2 &
                                  Y1 = L1.ⓑ{I}V & Y2 = L2.ⓑ{I}V.
#Y1 #Y2 #H elim (lfxs_inv_zero … H) -H *
/3 width=7 by ex3_4_intro, or_introl, or_intror, conj/
qed-.

lemma lfeq_inv_lref: ∀Y1,Y2,i. Y1 ≡[#⫯i] Y2 →
                     (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                     ∃∃I,L1,L2,V1,V2. L1 ≡[#i] L2 &
                                      Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#Y1 #Y2 #i #H elim (lfxs_inv_lref … H) -H *
/3 width=8 by ex3_5_intro, or_introl, or_intror, conj/
qed-.

lemma lfeq_inv_bind: ∀I,L1,L2,V,T,p. L1 ≡[ⓑ{p,I}V.T] L2 →
                     L1 ≡[V] L2 ∧ L1.ⓑ{I}V ≡[T] L2.ⓑ{I}V.
#I #L1 #L2 #V #T #p #H elim (lfxs_inv_bind … H) -H /2 width=3 by conj/
qed-.

lemma lfeq_inv_flat: ∀I,L1,L2,V,T. L1 ≡[ⓕ{I}V.T] L2 →
                     L1 ≡[V] L2 ∧ L1 ≡[T] L2.
#I #L1 #L2 #V #T #H elim (lfxs_inv_flat … H) -H /2 width=3 by conj/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lfeq_inv_zero_pair_sn: ∀I,Y2,L1,V. L1.ⓑ{I}V ≡[#0] Y2 →
                             ∃∃L2. L1 ≡[V] L2 & Y2 = L2.ⓑ{I}V.
#I #Y2 #L1 #V #H elim (lfxs_inv_zero_pair_sn … H) -H /2 width=3 by ex2_intro/
qed-.

lemma lfeq_inv_zero_pair_dx: ∀I,Y1,L2,V. Y1 ≡[#0] L2.ⓑ{I}V →
                             ∃∃L1. L1 ≡[V] L2 & Y1 = L1.ⓑ{I}V.
#I #Y1 #L2 #V #H elim (lfxs_inv_zero_pair_dx … H) -H
#L1 #X #HL12 #HX #H destruct /2 width=3 by ex2_intro/
qed-.

lemma lfeq_inv_lref_pair_sn: ∀I,Y2,L1,V1,i. L1.ⓑ{I}V1 ≡[#⫯i] Y2 →
                             ∃∃L2,V2. L1 ≡[#i] L2 & Y2 = L2.ⓑ{I}V2.
/2 width=2 by lfxs_inv_lref_pair_sn/ qed-.

lemma lfeq_inv_lref_pair_dx: ∀I,Y1,L2,V2,i. Y1 ≡[#⫯i] L2.ⓑ{I}V2 →
                             ∃∃L1,V1. L1 ≡[#i] L2 & Y1 = L1.ⓑ{I}V1.
/2 width=2 by lfxs_inv_lref_pair_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfeq_fwd_bind_sn: ∀I,L1,L2,V,T,p. L1 ≡[ⓑ{p,I}V.T] L2 → L1 ≡[V] L2.
/2 width=4 by lfxs_fwd_bind_sn/ qed-.

lemma lfeq_fwd_bind_dx: ∀I,L1,L2,V,T,p.
                        L1 ≡[ⓑ{p,I}V.T] L2 → L1.ⓑ{I}V ≡[T] L2.ⓑ{I}V.
/2 width=2 by lfxs_fwd_bind_dx/ qed-.

lemma lfeq_fwd_flat_sn: ∀I,L1,L2,V,T. L1 ≡[ⓕ{I}V.T] L2 → L1 ≡[V] L2.
/2 width=3 by lfxs_fwd_flat_sn/ qed-.

lemma lfeq_fwd_flat_dx: ∀I,L1,L2,V,T. L1 ≡[ⓕ{I}V.T] L2 → L1 ≡[T] L2.
/2 width=3 by lfxs_fwd_flat_dx/ qed-.

lemma lfeq_fwd_pair_sn: ∀I,L1,L2,V,T. L1 ≡[②{I}V.T] L2 → L1 ≡[V] L2.
/2 width=3 by lfxs_fwd_pair_sn/ qed-.

(* Advanceded forward lemmas with generic extension on referred entries *****)

lemma lfex_fwd_lfxs_refl: ∀R. (∀L. reflexive … (R L)) →
                          ∀L1,L2,T. L1 ≡[T] L2 → L1 ⦻*[R, T] L2.
/2 width=3 by lfxs_co/ qed-.

(* Basic_2A1: removed theorems 30: 
              lleq_ind lleq_inv_bind lleq_inv_flat lleq_fwd_length lleq_fwd_lref
              lleq_fwd_drop_sn lleq_fwd_drop_dx
              lleq_fwd_bind_sn lleq_fwd_bind_dx lleq_fwd_flat_sn lleq_fwd_flat_dx
              lleq_sort lleq_skip lleq_lref lleq_free lleq_gref lleq_bind lleq_flat
              lleq_refl lleq_Y lleq_sym lleq_ge_up lleq_ge lleq_bind_O llpx_sn_lrefl
              lleq_trans lleq_canc_sn lleq_canc_dx lleq_nlleq_trans nlleq_lleq_div
*)
