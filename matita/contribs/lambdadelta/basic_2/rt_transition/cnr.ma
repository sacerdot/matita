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

include "basic_2/notation/relations/prednormal_4.ma".
include "basic_2/rt_transition/cpr.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE R-TRANSITION **************************)

definition cnr (h) (G) (L): predicate term ≝ NF … (cpm h G L 0) (eq …).

interpretation
   "normality for context-sensitive r-transition (term)"
   'PRedNormal h G L T = (cnr h G L T).

(* Basic inversion lemmas ***************************************************)

lemma cnr_inv_abst (h) (p) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃ⓛ{p}V.T⦄ → ∧∧ ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃V⦄ & ⦃G, L.ⓛV⦄ ⊢ ➡[h] 𝐍⦃T⦄.
#h #p #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ{p}V2.T1) ?) -HVT1 /2 width=2 by cpr_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓛ{p}V1.T2) ?) -HVT1 /2 width=2 by cpm_bind/ -HT2 #H destruct //
]
qed-.

(* Basic_2A1: was: cnr_inv_abbr *)
lemma cnr_inv_abbr_neg (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃-ⓓV.T⦄ → ∧∧ ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃V⦄ & ⦃G, L.ⓓV⦄ ⊢ ➡[h] 𝐍⦃T⦄.
#h #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2 by cpr_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2 by cpm_bind/ -HT2 #H destruct //
]
qed-.

(* Basic_2A1: was: cnr_inv_eps *)
lemma cnr_inv_cast (h) (G) (L): ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃ⓝV.T⦄ → ⊥.
#h #G #L #V #T #H lapply (H T ?) -H
/2 width=4 by cpm_eps, discr_tpair_xy_y/
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_sort *)
lemma cnr_sort (h) (G) (L): ∀s. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃⋆s⦄.
#h #G #L #s #X #H
>(cpr_inv_sort1 … H) //
qed.

lemma cnr_gref (h) (G) (L): ∀l. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃§l⦄.
#h #G #L #l #X #H
>(cpr_inv_gref1 … H) //
qed.

(* Basic_1: was: nf2_abst *)
lemma cnr_abst (h) (p) (G) (L):
      ∀W,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃W⦄ → ⦃G, L.ⓛW⦄ ⊢ ➡[h] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃ⓛ{p}W.T⦄.
#h #p #G #L #W #T #HW #HT #X #H
elim (cpm_inv_abst1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
<(HW … HW0) -W0 <(HT … HT0) -T0 //
qed.

lemma cnr_abbr_neg (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃V⦄ → ⦃G, L.ⓓV⦄ ⊢ ➡[h] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃-ⓓV.T⦄.
#h #G #L #V #T #HV #HT #X #H
elim (cpm_inv_abbr1 … H) -H *
[ #V0 #T0 #HV0 #HT0 #H destruct
  <(HV … HV0) -V0 <(HT … HT0) -T0 //
| #T0 #_ #_ #H destruct
]
qed.


(* Basic_1: removed theorems 1: nf2_abst_shift *)
