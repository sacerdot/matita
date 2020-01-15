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

include "basic_2/notation/relations/predtystrong_4.ma".
include "static_2/syntax/teqx.ma".
include "basic_2/rt_transition/cpx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

definition csx (h) (G) (L): predicate term ≝
           SN … (cpx h G L) teqx.

interpretation
  "strong normalization for unbound context-sensitive parallel rt-transition (term)"
  'PRedTyStrong h G L T = (csx h G L T).

(* Basic eliminators ********************************************************)

lemma csx_ind (h) (G) (L) (Q:predicate …):
      (∀T1. ❪G,L❫ ⊢ ⬈*𝐒[h] T1 →
        (∀T2. ❪G,L❫ ⊢ T1 ⬈[h] T2 → (T1 ≛ T2 → ⊥) → Q T2) →
        Q T1
      ) →
      ∀T. ❪G,L❫ ⊢ ⬈*𝐒[h] T →  Q T.
#h #G #L #Q #H0 #T1 #H elim H -T1
/5 width=1 by SN_intro/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was just: sn3_pr2_intro *)
lemma csx_intro (h) (G) (L):
      ∀T1. (∀T2. ❪G,L❫ ⊢ T1 ⬈[h] T2 → (T1 ≛ T2 → ⊥) → ❪G,L❫ ⊢ ⬈*𝐒[h] T2) →
      ❪G,L❫ ⊢ ⬈*𝐒[h] T1.
/4 width=1 by SN_intro/ qed.

(* Basic forward lemmas *****************************************************)

fact csx_fwd_pair_sn_aux (h) (G) (L):
     ∀U. ❪G,L❫ ⊢ ⬈*𝐒[h] U →
     ∀I,V,T. U = ②[I]V.T → ❪G,L❫ ⊢ ⬈*𝐒[h] V.
#h #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #V2 #HLV2 #HV2
@(IH (②[I]V2.T)) -IH /2 width=3 by cpx_pair_sn/ -HLV2
#H elim (teqx_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_head *)
lemma csx_fwd_pair_sn (h) (G) (L):
      ∀I,V,T. ❪G,L❫ ⊢ ⬈*𝐒[h] ②[I]V.T → ❪G,L❫ ⊢ ⬈*𝐒[h] V.
/2 width=5 by csx_fwd_pair_sn_aux/ qed-.

fact csx_fwd_bind_dx_aux (h) (G) (L):
     ∀U. ❪G,L❫ ⊢ ⬈*𝐒[h] U →
     ∀p,I,V,T. U = ⓑ[p,I]V.T → ❪G,L.ⓑ[I]V❫ ⊢ ⬈*𝐒[h] T.
#h #G #L #U #H elim H -H #U0 #_ #IH #p #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓑ[p, I]V.T2)) -IH /2 width=3 by cpx_bind/ -HLT2
#H elim (teqx_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_bind *)
lemma csx_fwd_bind_dx (h) (G) (L):
      ∀p,I,V,T. ❪G,L❫ ⊢ ⬈*𝐒[h] ⓑ[p,I]V.T → ❪G,L.ⓑ[I]V❫ ⊢ ⬈*𝐒[h] T.
/2 width=4 by csx_fwd_bind_dx_aux/ qed-.

fact csx_fwd_flat_dx_aux (h) (G) (L):
     ∀U. ❪G,L❫ ⊢ ⬈*𝐒[h] U →
     ∀I,V,T. U = ⓕ[I]V.T → ❪G,L❫ ⊢ ⬈*𝐒[h] T.
#h #G #L #U #H elim H -H #U0 #_ #IH #I #V #T #H destruct
@csx_intro #T2 #HLT2 #HT2
@(IH (ⓕ[I]V.T2)) -IH /2 width=3 by cpx_flat/ -HLT2
#H elim (teqx_inv_pair … H) -H /2 width=1 by/
qed-.

(* Basic_1: was just: sn3_gen_flat *)
lemma csx_fwd_flat_dx (h) (G) (L):
      ∀I,V,T. ❪G,L❫ ⊢ ⬈*𝐒[h] ⓕ[I]V.T → ❪G,L❫ ⊢ ⬈*𝐒[h] T.
/2 width=5 by csx_fwd_flat_dx_aux/ qed-.

lemma csx_fwd_bind (h) (G) (L):
      ∀p,I,V,T. ❪G,L❫ ⊢ ⬈*𝐒[h] ⓑ[p,I]V.T →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒[h] V & ❪G,L.ⓑ[I]V❫ ⊢ ⬈*𝐒[h] T.
/3 width=3 by csx_fwd_pair_sn, csx_fwd_bind_dx, conj/ qed-.

lemma csx_fwd_flat (h) (G) (L):
      ∀I,V,T. ❪G,L❫ ⊢ ⬈*𝐒[h] ⓕ[I]V.T →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒[h] V & ❪G,L❫ ⊢ ⬈*𝐒[h] T.
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
