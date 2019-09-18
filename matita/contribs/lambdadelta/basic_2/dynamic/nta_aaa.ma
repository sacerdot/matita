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

include "basic_2/dynamic/cnv_aaa.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Forward lemmas with atomic arity assignment for terms ********************)

(* Note: this means that no type is a universe *)
lemma nta_fwd_aaa (h) (a) (G) (L):
      ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U → ∃∃A. ⦃G,L⦄ ⊢ T ⁝ A & ⦃G,L⦄ ⊢ U ⁝ A.
#h #a #G #L #T #U #H
elim (cnv_fwd_aaa … H) -H #A #H
elim (aaa_inv_cast … H) -H #HU #HT
/2 width=3 by ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: uses: ty3_predicative *)
lemma nta_abst_predicative (h) (a) (p) (G) (L):
      ∀W,T. ⦃G,L⦄ ⊢ ⓛ{p}W.T :[h,a] W → ⊥.
#h #a #p #G #L #W #T #H
elim (nta_fwd_aaa … H) -a -h #X #H #H1W
elim (aaa_inv_abst … H) -p #B #A #H2W #_ #H destruct -T
lapply (aaa_mono … H1W … H2W) -G -L -W #H
elim (discr_apair_xy_x … H)
qed-.

(* Basic_1: uses: ty3_repellent *)
theorem nta_abst_repellent (h) (a) (p) (G) (K):
        ∀W,T,U1. ⦃G,K⦄ ⊢ ⓛ{p}W.T :[h,a] U1 →
        ∀U2. ⦃G,K.ⓛW⦄ ⊢ T :[h,a] U2 → ⬆*[1] U1 ≘ U2 → ⊥.
#h #a #p #G #K #W #T #U1 #H1 #U2 #H2 #HU12
elim (nta_fwd_aaa … H2) -H2 #A2 #H2T #H2U2
elim (nta_fwd_aaa … H1) -H1 #X1 #H1 #HU1
elim (aaa_inv_abst … H1) -a -h -p #B #A1 #_ #H1T #H destruct
lapply (aaa_mono … H1T … H2T) -T #H destruct
lapply (aaa_inv_lifts … H2U2 (Ⓣ) … K … HU12)
[ /3 width=1 by drops_refl, drops_drop/ ] -W -U2 #H2U1
lapply (aaa_mono … HU1 … H2U1) -G -K -U1 #H
elim (discr_apair_xy_y … H)
qed-.
