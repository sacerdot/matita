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

include "basic_2/notation/relations/sn_5.ma".
include "basic_2/reduction/cnx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

definition csx: ∀h. sd h → relation3 genv lenv term ≝
                λh,g,G,L. SN … (cpx h g G L) (eq …).

interpretation
   "context-sensitive extended strong normalization (term)"
   'SN h g G L T = (csx h g G L T).

(* Basic eliminators ********************************************************)

lemma csx_ind: ∀h,g,G,L. ∀R:predicate term.
               (∀T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                     (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → R T2) →
                     R T1
               ) →
               ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → R T.
#h #g #G #L #R #H0 #T1 #H elim H -T1
/5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: sn3_pr2_intro *)
lemma csx_intro: ∀h,g,G,L,T1.
                 (∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → (T1 = T2 → ⊥) → ⦃G, L⦄ ⊢ ⬊*[h, g] T2) →
                 ⦃G, L⦄ ⊢ ⬊*[h, g] T1.
/4 width=1 by SN_intro/ qed.

lemma csx_cpx_trans: ∀h,g,G,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ⦃G, L⦄ ⊢ ⬊*[h, g] T2.
#h #g #G #L #T1 #H @(csx_ind … H) -T1 #T1 #HT1 #IHT1 #T2 #HLT12
elim (eq_term_dec T1 T2) #HT12 destruct /3 width=4 by/
qed-.

(* Basic_1: was just: sn3_nf2 *)
lemma cnx_csx: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
/2 width=1 by NF_to_SN/ qed.

lemma csx_sort: ∀h,g,G,L,k. ⦃G, L⦄ ⊢ ⬊*[h, g] ⋆k.
#h #g #G #L #k elim (deg_total h g k)
#l generalize in match k; -k @(nat_ind_plus … l) -l /3 width=6 by cnx_csx, cnx_sort/
#l #IHl #k #Hkl lapply (deg_next_SO … Hkl) -Hkl
#Hkl @csx_intro #X #H #HX elim (cpx_inv_sort1 … H) -H
[ #H destruct elim HX //
| -HX * #l0 #_ #H destruct -l0 /2 width=1 by/
]
qed.

(* Basic_1: was just: sn3_cast *)
lemma csx_cast: ∀h,g,G,L,W. ⦃G, L⦄ ⊢ ⬊*[h, g] W →
                ∀T. ⦃G, L⦄ ⊢ ⬊*[h, g] T → ⦃G, L⦄ ⊢ ⬊*[h, g] ⓝW.T.
#h #g #G #L #W #HW @(csx_ind … HW) -W #W #HW #IHW #T #HT @(csx_ind … HT) -T #T #HT #IHT
@csx_intro #X #H1 #H2
elim (cpx_inv_cast1 … H1) -H1
[ * #W0 #T0 #HLW0 #HLT0 #H destruct
  elim (eq_false_inv_tpair_sn … H2) -H2
  [ /3 width=3 by csx_cpx_trans/
  | -HLW0 * #H destruct /3 width=1 by/
  ]
|2,3: /3 width=3 by csx_cpx_trans/
]
qed.

(* Basic forward lemmas *****************************************************)

fact csx_fwd_pair_sn_aux: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀I,V,T. U = ②{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] V.
#h #g #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #V2 #HLV2 #HV2
@(IH (②{I}V2.T)) -IH /2 width=3 by cpx_pair_sn/ -HLV2
#H destruct /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_head *)
lemma csx_fwd_pair_sn: ∀h,g,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ②{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] V.
/2 width=5 by csx_fwd_pair_sn_aux/ qed-.

fact csx_fwd_bind_dx_aux: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀a,I,V,T. U = ⓑ{a,I}V.T → ⦃G, L.ⓑ{I}V⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #U #H elim H -H #U0 #_ #IH #a #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓑ{a,I}V.T2)) -IH /2 width=3 by cpx_bind/ -HLT2
#H destruct /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_bind *)
lemma csx_fwd_bind_dx: ∀h,g,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓑ{a,I}V.T → ⦃G, L.ⓑ{I}V⦄ ⊢ ⬊*[h, g] T.
/2 width=4 by csx_fwd_bind_dx_aux/ qed-.

fact csx_fwd_flat_dx_aux: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ ⬊*[h, g] U →
                          ∀I,V,T. U = ⓕ{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓕ{I}V.T2)) -IH /2 width=3 by cpx_flat/ -HLT2
#H destruct /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_flat *)
lemma csx_fwd_flat_dx: ∀h,g,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓕ{I}V.T → ⦃G, L⦄ ⊢ ⬊*[h, g] T.
/2 width=5 by csx_fwd_flat_dx_aux/ qed-.

lemma csx_fwd_bind: ∀h,g,a,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓑ{a,I}V.T →
                    ⦃G, L⦄ ⊢ ⬊*[h, g] V ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ⬊*[h, g] T.
/3 width=3 by csx_fwd_pair_sn, csx_fwd_bind_dx, conj/ qed-.

lemma csx_fwd_flat: ∀h,g,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬊*[h, g] ⓕ{I}V.T →
                    ⦃G, L⦄ ⊢ ⬊*[h, g] V ∧ ⦃G, L⦄ ⊢ ⬊*[h, g] T.
/3 width=3 by csx_fwd_pair_sn, csx_fwd_flat_dx, conj/ qed-.

(* Basic_1: removed theorems 14:
            sn3_cdelta
            sn3_gen_cflat sn3_cflat sn3_cpr3_trans sn3_shift sn3_change
            sn3_appl_cast sn3_appl_beta sn3_appl_lref sn3_appl_abbr
            sn3_appl_appls sn3_bind sn3_appl_bind sn3_appls_bind
*)
