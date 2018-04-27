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

include "basic_2/notation/relations/predtystrong_5.ma".
include "basic_2/syntax/tdeq.ma".
include "basic_2/rt_transition/cpx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

definition csx: ∀h. sd h → relation3 genv lenv term ≝
                λh,o,G,L. SN … (cpx h G L) (tdeq h o …).

interpretation
   "strong normalization for unbound context-sensitive parallel rt-transition (term)"
   'PRedTyStrong h o G L T = (csx h o G L T).

(* Basic eliminators ********************************************************)

lemma csx_ind: ∀h,o,G,L. ∀R:predicate term.
               (∀T1. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄ →
                     (∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → (T1 ≛[h, o] T2 → ⊥) → R T2) →
                     R T1
               ) →
               ∀T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ → R T.
#h #o #G #L #R #H0 #T1 #H elim H -T1
/5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: sn3_pr2_intro *)
lemma csx_intro: ∀h,o,G,L,T1.
                 (∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → (T1 ≛[h, o] T2 → ⊥) → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T2⦄) →
                 ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T1⦄.
/4 width=1 by SN_intro/ qed.

(* Basic forward lemmas *****************************************************)

fact csx_fwd_pair_sn_aux: ∀h,o,G,L,U. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃U⦄ →
                          ∀I,V,T. U = ②{I}V.T → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄.
#h #o #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #V2 #HLV2 #HV2
@(IH (②{I}V2.T)) -IH /2 width=3 by cpx_pair_sn/ -HLV2
#H elim (tdeq_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_head *)
lemma csx_fwd_pair_sn: ∀h,o,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃②{I}V.T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄.
/2 width=5 by csx_fwd_pair_sn_aux/ qed-.

fact csx_fwd_bind_dx_aux: ∀h,o,G,L,U. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃U⦄ →
                          ∀p,I,V,T. U = ⓑ{p,I}V.T → ⦃G, L.ⓑ{I}V⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
#h #o #G #L #U #H elim H -H #U0 #_ #IH #p #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓑ{p,I}V.T2)) -IH /2 width=3 by cpx_bind/ -HLT2
#H elim (tdeq_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_bind *)
lemma csx_fwd_bind_dx: ∀h,o,p,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓑ{p,I}V.T⦄ → ⦃G, L.ⓑ{I}V⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/2 width=4 by csx_fwd_bind_dx_aux/ qed-.

fact csx_fwd_flat_dx_aux: ∀h,o,G,L,U. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃U⦄ →
                          ∀I,V,T. U = ⓕ{I}V.T → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
#h #o #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓕ{I}V.T2)) -IH /2 width=3 by cpx_flat/ -HLT2
#H elim (tdeq_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_flat *)
lemma csx_fwd_flat_dx: ∀h,o,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓕ{I}V.T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/2 width=5 by csx_fwd_flat_dx_aux/ qed-.

lemma csx_fwd_bind: ∀h,o,p,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓑ{p,I}V.T⦄ →
                    ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄ ∧ ⦃G, L.ⓑ{I}V⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/3 width=3 by csx_fwd_pair_sn, csx_fwd_bind_dx, conj/ qed-.

lemma csx_fwd_flat: ∀h,o,I,G,L,V,T. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⓕ{I}V.T⦄ →
                    ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃V⦄ ∧ ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/3 width=3 by csx_fwd_pair_sn, csx_fwd_flat_dx, conj/ qed-.

(* Basic_1: removed theorems 14:
            sn3_cdelta
            sn3_gen_cflat sn3_cflat sn3_cpr3_trans sn3_shift sn3_change
            sn3_appl_cast sn3_appl_beta sn3_appl_lref sn3_appl_abbr
            sn3_appl_appls sn3_bind sn3_appl_bind sn3_appls_bind
*)
(* Basic_2A1: removed theorems 6:
              csxa_ind csxa_intro csxa_cpxs_trans csxa_intro_cpx 
              csx_csxa csxa_csx
*)
