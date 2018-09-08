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

include "static_2/syntax/tdpos.ma".
include "basic_2/dynamic/cnv_cpm_tdeq.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas with positive rt-transition for terms *********************)

lemma cpm_tdeq_fwd_tdpos_sn (a) (h) (o) (n) (G):
                            ∀L,T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
                            ∀T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → T1 ≛[h,o] T2 → 𝐏[h,o]⦃T1⦄ →
                            ∧∧ T1 = T2 & 0 = n.
#a #h #o #n #G #L #T1 #H0 #T2 #H1 #H2
@(cpm_tdeq_ind … H0 … H1 H2) -L -T1 -T2
[ /2 width=1 by conj/
| #L #s #_ #H1 #H
  elim (tdpos_inv_sort … H) -H #d #H2
  lapply (deg_mono … H2 H1) -H1 -H2 #H destruct
| #p #I #L #V #T1 #_ #_ #T2 #_ #_ #IH #H
  elim (tdpos_inv_pair … H) -H #_ #HT1
  elim IH // -IH -HT1 #H1 #H2 destruct
  /2 width=1 by conj/
| #m #_ #L #V #_ #W #_ #q #T1 #U1 #_ #_ #T2 #_ #_ #IH #H -a -m -q -G -L -W -U1
  elim (tdpos_inv_pair … H) -H #_ #HT1
  elim IH // -IH -HT1 #H1 #H2 destruct
  /2 width=1 by conj/
| #L #U0 #U1 #T1 #_ #_ #U2 #_ #_ #_ #T2 #_ #_ #_ #IHU #IHT #H
  elim (tdpos_inv_pair … H) -H #HU1 #HT1
  elim IHU // -IHU -HU1 #H1 #H2 destruct
  elim IHT // -IHT -HT1 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpm_fwd_tdpos_sn (a) (h) (o) (n) (G) (L):
                       ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] → 𝐏[h,o]⦃T1⦄ →
                       ∀T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 →
                       ∨∨ ∧∧ T1 = T2 & 0 = n | (T1 ≛[h,o] T2 → ⊥).
#a #h #o #n #G #L #T1 #H1T1 #H2T1 #T2 #HT12
elim (tdeq_dec h o T1 T2) #H
/3 width=9 by cpm_tdeq_fwd_tdpos_sn, or_intror, or_introl/
qed-.
