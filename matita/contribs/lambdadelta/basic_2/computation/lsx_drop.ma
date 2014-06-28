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

include "basic_2/multiple/lleq_drop.ma".
include "basic_2/reduction/lpx_drop.ma".
include "basic_2/computation/lsx.ma".

(* SN EXTENDED STRONGLY NORMALIZING LOCAL ENVIRONMENTS **********************)

(* Advanced properties ******************************************************)

lemma lsx_lref_free: ∀h,g,G,L,d,i. |L| ≤ i → G ⊢ ⬊*[h, g, #i, d] L.
#h #g #G #L1 #d #i #HL1 @lsx_intro
#L2 #HL12 #H elim H -H
/4 width=6 by lpx_fwd_length, lleq_free, le_repl_sn_conf_aux/
qed.

lemma lsx_lref_skip: ∀h,g,G,L,d,i. yinj i < d → G ⊢ ⬊*[h, g, #i, d] L.
#h #g #G #L1 #d #i #HL1 @lsx_intro
#L2 #HL12 #H elim H -H
/3 width=4 by lpx_fwd_length, lleq_skip/
qed.

(* Advanced forward lemmas **************************************************)

lemma lsx_fwd_lref_be: ∀h,g,I,G,L,d,i. d ≤ yinj i → G ⊢ ⬊*[h, g, #i, d] L →
                       ∀K,V. ⇩[i] L ≡ K.ⓑ{I}V → G ⊢ ⬊*[h, g, V, 0] K.
#h #g #I #G #L #d #i #Hdi #H @(lsx_ind … H) -L
#L1 #_ #IHL1 #K1 #V #HLK1 @lsx_intro
#K2 #HK12 #HnK12 lapply (drop_fwd_drop2 … HLK1)
#H2LK1 elim (drop_lpx_trans … H2LK1 … HK12) -H2LK1 -HK12
#L2 #HL12 #H2LK2 #H elim (leq_drop_conf_be … H … HLK1) -H /2 width=1 by ylt_inj/
#Y #_ #HLK2 lapply (drop_fwd_drop2 … HLK2)
#HY lapply (drop_mono … HY … H2LK2) -HY -H2LK2 #H destruct
/4 width=10 by lleq_inv_lref_ge/
qed-.

(* Properties on relocation *************************************************)

lemma lsx_lift_le: ∀h,g,G,K,T,U,dt,d,e. dt ≤ yinj d →
                   ⇧[d, e] T ≡ U → G ⊢ ⬊*[h, g, T, dt] K →
                   ∀L. ⇩[Ⓕ, d, e] L ≡ K → G ⊢ ⬊*[h, g, U, dt] L.
#h #g #G #K #T #U #dt #d #e #Hdtd #HTU #H @(lsx_ind … H) -K
#K1 #_ #IHK1 #L1 #HLK1 @lsx_intro
#L2 #HL12 #HnU elim (lpx_drop_conf … HLK1 … HL12) -HL12
/4 width=10 by lleq_lift_le/
qed-.

lemma lsx_lift_ge: ∀h,g,G,K,T,U,dt,d,e. yinj d ≤ dt →
                   ⇧[d, e] T ≡ U → G ⊢ ⬊*[h, g, T, dt] K →
                   ∀L. ⇩[Ⓕ, d, e] L ≡ K → G ⊢ ⬊*[h, g, U, dt + e] L.
#h #g #G #K #T #U #dt #d #e #Hddt #HTU #H @(lsx_ind … H) -K
#K1 #_ #IHK1 #L1 #HLK1 @lsx_intro
#L2 #HL12 #HnU elim (lpx_drop_conf … HLK1 … HL12) -HL12
/4 width=9 by lleq_lift_ge/
qed-.

(* Inversion lemmas on relocation *******************************************)

lemma lsx_inv_lift_le: ∀h,g,G,L,T,U,dt,d,e. dt ≤ yinj d →
                       ⇧[d, e] T ≡ U → G ⊢ ⬊*[h, g, U, dt] L →
                       ∀K. ⇩[Ⓕ, d, e] L ≡ K → G ⊢ ⬊*[h, g, T, dt] K.
#h #g #G #L #T #U #dt #d #e #Hdtd #HTU #H @(lsx_ind … H) -L
#L1 #_ #IHL1 #K1 #HLK1 @lsx_intro
#K2 #HK12 #HnT elim (drop_lpx_trans … HLK1 … HK12) -HK12
/4 width=10 by lleq_inv_lift_le/
qed-.

lemma lsx_inv_lift_be: ∀h,g,G,L,T,U,dt,d,e. yinj d ≤ dt → dt ≤ d + e →
                       ⇧[d, e] T ≡ U → G ⊢ ⬊*[h, g, U, dt] L →
                       ∀K. ⇩[Ⓕ, d, e] L ≡ K → G ⊢ ⬊*[h, g, T, d] K.
#h #g #G #L #T #U #dt #d #e #Hddt #Hdtde #HTU #H @(lsx_ind … H) -L
#L1 #_ #IHL1 #K1 #HLK1 @lsx_intro
#K2 #HK12 #HnT elim (drop_lpx_trans … HLK1 … HK12) -HK12
/4 width=11 by lleq_inv_lift_be/
qed-.

lemma lsx_inv_lift_ge: ∀h,g,G,L,T,U,dt,d,e. yinj d + yinj e ≤ dt →
                       ⇧[d, e] T ≡ U → G ⊢ ⬊*[h, g, U, dt] L →
                       ∀K. ⇩[Ⓕ, d, e] L ≡ K → G ⊢ ⬊*[h, g, T, dt-e] K.
#h #g #G #L #T #U #dt #d #e #Hdedt #HTU #H @(lsx_ind … H) -L
#L1 #_ #IHL1 #K1 #HLK1 @lsx_intro
#K2 #HK12 #HnT elim (drop_lpx_trans … HLK1 … HK12) -HK12
/4 width=9 by lleq_inv_lift_ge/
qed-.
