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

include "basic_2/static/sta_lift.ma".
include "basic_2/unfold/lstas.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on relocation *************************************************)

lemma lstas_lift: ∀h,G,l. l_liftable (llstar … (sta h G) l).
/3 width=10 by l_liftable_llstar, sta_lift/ qed.

(* Inversion lemmas on relocation *******************************************)

lemma lstas_inv_lift1: ∀h,G,l. l_deliftable_sn (llstar … (sta h G) l).
/3 width=6 by l_deliftable_sn_llstar, sta_inv_lift1/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lstas_inv_lref1: ∀h,G,L,U,i,l. ⦃G, L⦄ ⊢ #i •*[h, l+1] U →
                       (∃∃K,V,W. ⇩[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, l+1] W &
                                 ⇧[0, i+1] W ≡ U
                       ) ∨
                       (∃∃K,W,V,V0. ⇩[i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W •[h] V0 &
                                    ⦃G, K⦄ ⊢ W •*[h, l] V & ⇧[0, i+1] V ≡ U
                        ).
#h #G #L #U #i #l #H elim (lstas_inv_step_sn … H) -H
#X #H #HXU elim (sta_inv_lref1 … H) -H
* #K #V #W #HLK #HVW #HWX
lapply (drop_fwd_drop2 … HLK) #H0LK
elim (lstas_inv_lift1 … HXU … H0LK … HWX) -H0LK -X
/4 width=8 by lstas_step_sn, ex4_4_intro, ex3_3_intro, or_introl, or_intror/
qed-.

(* Advanced forward lemmas **************************************************)

lemma lstas_fwd_correct: ∀h,G,L,T1,U1. ⦃G, L⦄ ⊢ T1 •[h] U1 →
                         ∀T2,l. ⦃G, L⦄ ⊢ T1 •*[h, l] T2 →
                         ∃U2. ⦃G, L⦄ ⊢ T2 •[h] U2.
#h #G #L #T1 #U1 #HTU1 #T2 #l #H @(lstas_ind_dx … H) -l -T2 /2 width=3 by ex_intro/ -HTU1
#l #T #T2 #_ #HT2 #_ -T1 -U1 -l
elim (sta_fwd_correct … HT2) -T /2 width=2 by ex_intro/
qed-.

(* Advanced properties ******************************************************)

lemma lstas_total: ∀h,G,L,T,U. ⦃G, L⦄ ⊢ T •[h] U →
                   ∀l. ∃U0. ⦃G, L⦄ ⊢ T •*[h, l] U0.
#h #G #L #T #U #HTU #l @(nat_ind_plus … l) -l /2 width=2 by ex_intro/
#l * #U0 #HTU0 elim (lstas_fwd_correct … HTU … HTU0) -U
/3 width=4 by lstas_step_dx, ex_intro/
qed-.

lemma lstas_ldef: ∀h,G,L,K,V,i. ⇩[i] L ≡ K.ⓓV →
                  ∀W,l. ⦃G, K⦄ ⊢ V •*[h, l+1] W →
                  ∀U. ⇧[0, i+1] W ≡ U → ⦃G, L⦄ ⊢ #i •*[h, l+1] U.
#h #G #L #K #V #i #HLK #W #l #HVW #U #HWU
lapply (drop_fwd_drop2 … HLK)
elim (lstas_inv_step_sn … HVW) -HVW #W0
elim (lift_total W0 0 (i+1)) /3 width=12 by lstas_step_sn, sta_ldef, lstas_lift/
qed.

lemma lstas_ldec: ∀h,G,L,K,W,i. ⇩[i] L ≡ K.ⓛW → ∀V0. ⦃G, K⦄ ⊢ W •[h] V0 →
                  ∀V,l. ⦃G, K⦄ ⊢ W •*[h, l] V →
                  ∀U. ⇧[0, i+1] V ≡ U → ⦃G, L⦄ ⊢ #i •*[h, l+1] U.
#h #G #L #K #W #i #HLK #V0 #HWV0 #V #l #HWV #U #HVU
lapply (drop_fwd_drop2 … HLK) #H
elim (lift_total W 0 (i+1)) /3 width=12 by lstas_step_sn, sta_ldec, lstas_lift/
qed.
