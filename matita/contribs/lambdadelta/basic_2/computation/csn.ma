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

include "basic_2/notation/relations/sn_4.ma".
include "basic_2/reduction/cnx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

definition csn: ∀h. sd h → lenv → predicate term ≝
                λh,g,L. SN … (cpx h g L) (eq …).

interpretation
   "context-sensitive extended strong normalization (term)"
   'SN h g L T = (csn h g L T).

(* Basic eliminators ********************************************************)

lemma csn_ind: ∀h,g,L. ∀R:predicate term.
               (∀T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                     (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → R T2) →
                     R T1
               ) →
               ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R T.
#h #g #L #R #H0 #T1 #H elim H -T1 #T1 #HT1 #IHT1
@H0 -H0 /3 width=1/ -IHT1 /4 width=1/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: sn3_pr2_intro *)
lemma csn_intro: ∀h,g,L,T1.
                 (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, g] T2) →
                 ⦃G, L⦄ ⊢ ⬊*[h, g] T1.
/4 width=1/ qed.

lemma csn_cpx_trans: ∀h,g,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ⦃G, L⦄ ⊢ ⬊*[h, g] T2.
#h #g #L #T1 #H elim H -T1 #T1 #HT1 #IHT1 #T2 #HLT12
@csn_intro #T #HLT2 #HT2
elim (term_eq_dec T1 T2) #HT12
[ -IHT1 -HLT12 destruct /3 width=1/
| -HT1 -HT2 /3 width=4/
qed-.

(* Basic_1: was just: sn3_nf2 *)
lemma cnx_csn: ∀h,g,L,T. ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄ → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
/2 width=1/ qed.

lemma cnx_sort: ∀h,g,L,k. ⦃G, L⦄ ⊢ ⬊*[h, g] ⋆k.
#h #g #L #k elim (deg_total h g k)
#l generalize in match k; -k @(nat_ind_plus … l) -l /3 width=1/
#l #IHl #k #Hkl lapply (deg_next_SO … Hkl) -Hkl
#Hkl @csn_intro #X #H #HX elim (cpx_inv_sort1 … H) -H
[ #H destruct elim HX //
| -HX * #l0 #_ #H destruct -l0 /2 width=1/
]
qed.

(* Basic_1: was just: sn3_cast *)
lemma csn_cast: ∀h,g,L,W. ⦃G, L⦄ ⊢ ⬊*[h, g] W →
                ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓝW.T.
#h #g #L #W #HW @(csn_ind … HW) -W #W #HW #IHW #T #HT @(csn_ind … HT) -T #T #HT #IHT
@csn_intro #X #H1 #H2
elim (cpx_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ /3 width=3 by csn_cpx_trans/
  | -HLW0 * #H destruct /3 width=1/
  ]
|2,3: /3 width=3 by csn_cpx_trans/
]
qed.

(* Basic forward lemmas *****************************************************)

fact csn_fwd_pair_sn_aux: ∀h,g,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀I,V,T. U = ②{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] V.
#h #g #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csn_intro #V2 #HLV2 #HV2
@(IH (②{I}V2.T)) -IH // /2 width=1/ -HLV2 #H destruct /2 width=1/
qed-.

(* Basic_1: was just: sn3_gen_head *)
lemma csn_fwd_pair_sn: ∀h,g,I,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ②{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] V.
/2 width=5 by csn_fwd_pair_sn_aux/ qed-.

fact csn_fwd_bind_dx_aux: ∀h,g,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀a,I,V,T. U = ⓑ{a,I}V.T → ⦃h, L.ⓑ{I}V⦄ ⊢ ⬊*[h, g] T.
#h #g #L #U #H elim H -H #U0 #_ #IH #a #I #V #T #H destruct
@csn_intro #T2 #HLT2 #HT2
@(IH (ⓑ{a,I} V. T2)) -IH // /2 width=1/ -HLT2 #H destruct /2 width=1/
qed-.

(* Basic_1: was just: sn3_gen_bind *)
lemma csn_fwd_bind_dx: ∀h,g,a,I,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓑ{a,I}V.T → ⦃h, L.ⓑ{I}V⦄ ⊢ ⬊*[h, g] T.
/2 width=4 by csn_fwd_bind_dx_aux/ qed-.

fact csn_fwd_flat_dx_aux: ∀h,g,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀I,V,T. U = ⓕ{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csn_intro #T2 #HLT2 #HT2
@(IH (ⓕ{I}V.T2)) -IH // /2 width=1/ -HLT2 #H destruct /2 width=1/
qed-.

(* Basic_1: was just: sn3_gen_flat *)
lemma csn_fwd_flat_dx: ∀h,g,I,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓕ{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
/2 width=5 by csn_fwd_flat_dx_aux/ qed-.

(* Basic_1: removed theorems 14:
            sn3_cdelta
            sn3_gen_cflat sn3_cflat sn3_cpr3_trans sn3_shift sn3_change
            sn3_appl_cast sn3_appl_beta sn3_appl_lref sn3_appl_abbr
            sn3_appl_appls sn3_bind sn3_appl_bind sn3_appls_bind
*)
