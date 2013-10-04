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

include "basic_2/static/ssta_lift.ma".
include "basic_2/unfold/lsstas.ma".

(* NAT-ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *****************)

(* Properties on relocation *************************************************)

lemma lsstas_lift: ∀h,g,G,l. l_liftable (llstar … (ssta h g G) l).
/2 width=1/ qed.

(* Inversion lemmas on relocation *******************************************)

lemma lsstas_inv_lift1: ∀h,g,G,l. l_deliftable_sn (llstar … (ssta h g G) l).
/3 width=5 by l_deliftable_sn_llstar, ssta_inv_lift1/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsstas_inv_lref1: ∀h,g,G,L,U,i,l. ⦃G, L⦄ ⊢ #i •*[h, g, l+1] U →
                        (∃∃K,V,W. ⇩[0, i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V •*[h, g, l+1] W &
                                  ⇧[0, i + 1] W ≡ U
                        ) ∨
                        (∃∃K,W,V,l0. ⇩[0, i] L ≡ K.ⓛW & ⦃G, K⦄ ⊢ W ▪[h, g] l0 &
                                     ⦃G, K⦄ ⊢ W •*[h, g, l] V & ⇧[0, i + 1] V ≡ U
                        ).
#h #g #G #L #U #i #l #H elim (lsstas_inv_step_sn … H) -H
#X #H #HXU elim (ssta_inv_lref1 … H) -H
* #K [ #V #W | #W #l0 ] #HLK [ #HVW | #HWl0 ] #HWX
lapply (ldrop_fwd_ldrop2 … HLK) #H0LK
elim (lsstas_inv_lift1 … HXU … H0LK … HWX) -H0LK -X /3 width=8/ /4 width=6/
qed-.

(* Advanced forward lemmas **************************************************)

lemma lsstas_fwd_correct: ∀h,g,G,L,T1,U1. ⦃G, L⦄ ⊢ T1 •[h, g] U1 →
                          ∀T2,l. ⦃G, L⦄ ⊢ T1 •*[h, g, l] T2 →
                          ∃U2. ⦃G, L⦄ ⊢ T2 •[h, g] U2.
#h #g #G #L #T1 #U1 #HTU1 #T2 #l #H @(lsstas_ind_dx … H) -l -T2 [ /2 width=3/ ] -HTU1
#l #T #T2 #_ #HT2 #_ -T1 -U1 -l
elim (ssta_fwd_correct … HT2) -T /2 width=2/
qed-.

(* Advanced properties ******************************************************)

lemma lsstas_total: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T •[h, g] U →
                    ∀l. ∃U0. ⦃G, L⦄ ⊢ T •*[h, g, l] U0.
#h #g #G #L #T #U #HTU #l @(nat_ind_plus … l) -l [ /2 width=2/ ]
#l * #U0 #HTU0
elim (lsstas_fwd_correct … HTU … HTU0) -U /3 width=4/
qed-.

lemma lsstas_ldef: ∀h,g,G,L,K,V,i. ⇩[0, i] L ≡ K.ⓓV →
                   ∀W,l. ⦃G, K⦄ ⊢ V •*[h, g, l+1] W →
                   ∀U. ⇧[0, i+1] W ≡ U → ⦃G, L⦄ ⊢ #i •*[h, g, l+1] U.
#h #g #G #L #K #V #i #HLK #W #l #HVW #U #HWU
lapply (ldrop_fwd_ldrop2 … HLK)
elim (lsstas_inv_step_sn … HVW) -HVW #W0
elim (lift_total W0 0 (i+1)) /3 width=11/
qed.

lemma lsstas_ldec: ∀h,g,G,L,K,W,i. ⇩[0, i] L ≡ K.ⓛW → ∀l0. ⦃G, K⦄ ⊢ W ▪[h, g] l0 →
                   ∀V,l. ⦃G, K⦄ ⊢ W •*[h, g, l] V →
                   ∀U. ⇧[0, i+1] V ≡ U → ⦃G, L⦄ ⊢ #i •*[h, g, l+1] U.
#h #g #G #L #K #W #i #HLK #T #HWT #V #l #HWV #U #HVU
lapply (ldrop_fwd_ldrop2 … HLK) #H
elim (lift_total W 0 (i+1)) /3 width=11/
qed.

(* Properties on degree assignment for terms ********************************)

lemma lsstas_da_conf: ∀h,g,G,L,T,U,l1. ⦃G, L⦄ ⊢ T •*[h, g, l1] U →
                      ∀l2. ⦃G, L⦄ ⊢ T ▪[h, g] l2 → ⦃G, L⦄ ⊢ U ▪[h, g] l2-l1.
#h #g #G #L #T #U #l1 #H @(lsstas_ind_dx … H) -U -l1 //
#l1 #U #U0 #_ #HU0 #IHTU #l2 #HT
<minus_plus /3 width=3 by ssta_da_conf/
qed-.
