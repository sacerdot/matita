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

include "basic_2/rt_equivalence/cpcs_cprs.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties with r-equivalence for terms **********************************)

lemma nta_conv_cnv (a) (h) (G) (L) (T):
                   ∀U1. ⦃G,L⦄ ⊢ T :[a,h] U1 →
                   ∀U2. ⦃G,L⦄  ⊢ U1 ⬌*[h] U2 → ⦃G,L⦄ ⊢ U2 ![a,h] → ⦃G,L⦄ ⊢ T :[a,h] U2.
#a #h #G #L #T #U1 #H1 #U2 #HU12 #HU2
elim (cnv_inv_cast … H1) -H1 #X1 #HU1 #HT #HUX1 #HTX1
lapply (cpcs_cprs_conf … HUX1 … HU12) -U1 #H
elim (cpcs_inv_cprs … H) -H #X2 #HX12 #HU12
/3 width=5 by cnv_cast, cpms_cprs_trans/
qed-.

(* Basic_1: was by definition: ty3_conv *)
(* Basic_2A1: was by definition: nta_conv ntaa_conv *)
lemma nta_conv (a) (h) (G) (L) (T):
               ∀U1. ⦃G,L⦄ ⊢ T :[a,h] U1 →
               ∀U2. ⦃G,L⦄  ⊢ U1 ⬌*[h] U2 →
               ∀W2. ⦃G,L⦄ ⊢ U2 :[a,h] W2 → ⦃G,L⦄ ⊢ T :[a,h] U2.
#a #h #G #L #T #U1 #H1 #U2 #HU12 #W2 #H2
/3 width=3 by nta_conv_cnv, nta_fwd_cnv_sn/
qed-.

(* Inversion lemmas with r-equivalence for terms ***************************)

(* Basic_1: was: ty3_gen_sort *)
(* Basic_2A1: was: nta_inv_sort1 *)
lemma nta_inv_sort_sn (a) (h) (G) (L) (X2):
      ∀s. ⦃G,L⦄ ⊢ ⋆s :[a,h] X2 →
      ∧∧ ⦃G,L⦄ ⊢ ⋆(next h s) ⬌*[h] X2 & ⦃G,L⦄ ⊢ X2 ![a,h].
#a #h #G #L #X2 #s #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #_ #HX21 #H
lapply (cpms_inv_sort1 … H) -H #H destruct
/3 width=1 by cpcs_cprs_sn, conj/
qed-.

lemma nta_inv_ldec_sn_cnv (a) (h) (G) (K) (V):
      ∀X2. ⦃G,K.ⓛV⦄ ⊢ #0 :[a,h] X2 →
      ∃∃U. ⦃G,K⦄ ⊢ V ![a,h] & ⬆*[1] V ≘ U & ⦃G,K.ⓛV⦄ ⊢ U ⬌*[h] X2 & ⦃G,K.ⓛV⦄ ⊢ X2 ![a,h].
#a #h #G #Y #X #X2 #H
elim (cnv_inv_cast … H) -H #X1 #HX2 #H1 #HX21 #H2
elim (cnv_inv_zero … H1) -H1 #Z #K #V #HV #H destruct
elim (cpms_inv_ell_sn … H2) -H2 *
[ #_ #H destruct
| #m #W #HVW #HWX1 #H destruct
  elim (lifts_total V (𝐔❴1❵)) #U #HVU
  lapply (cpms_lifts_bi … HVW (Ⓣ) … (K.ⓛV) … HVU … HWX1) -W
  [ /3 width=1 by drops_refl, drops_drop/ ] #HUX1
  /3 width=5 by cprs_div, ex4_intro/
]
qed-.
