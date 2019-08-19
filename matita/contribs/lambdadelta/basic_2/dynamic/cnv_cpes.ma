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

include "basic_2/rt_equivalence/cpes.ma".
include "basic_2/dynamic/cnv_aaa.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with t-bound rt-equivalence for terms *************************)

lemma cnv_appl_cpes (a) (h) (G) (L):
      ∀n. yinj n < a →
      ∀V. ⦃G,L⦄ ⊢ V ![a,h] → ∀T. ⦃G,L⦄ ⊢ T ![a,h] →
      ∀W. ⦃G,L⦄ ⊢ V ⬌*[h,1,0] W →
      ∀p,U. ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W.U → ⦃G,L⦄ ⊢ ⓐV.T ![a,h].
#a #h #G #L #n #Hn #V #HV #T #HT #W *
/4 width=11 by cnv_appl, cpms_cprs_trans, cpms_bind/
qed.

lemma cnv_cast_cpes (a) (h) (G) (L):
      ∀U. ⦃G,L⦄ ⊢ U ![a,h] →
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ⦃G,L⦄ ⊢ U ⬌*[h,0,1] T → ⦃G,L⦄ ⊢ ⓝU.T ![a,h].
#a #h #G #L #U #HU #T #HT * /2 width=3 by cnv_cast/
qed.

(* Inversion lemmas with t-bound rt-equivalence for terms *******************)

lemma cnv_inv_appl_cpes (a) (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T ![a,h] →
      ∃∃n,p,W,U. yinj n < a & ⦃G,L⦄ ⊢ V ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
                 ⦃G,L⦄ ⊢ V ⬌*[h,1,0] W & ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W.U.
#a #h #G #L #V #T #H
elim (cnv_inv_appl … H) -H #n #p #W #U #Hn #HV #HT #HVW #HTU
/3 width=7 by cpms_div, ex5_4_intro/
qed-.

lemma cnv_inv_appl_pred_cpes (a) (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ⓐV.T ![yinj a,h] →
      ∃∃p,W,U. ⦃G,L⦄ ⊢ V ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
               ⦃G,L⦄ ⊢ V ⬌*[h,1,0] W & ⦃G,L⦄ ⊢ T ➡*[↓a,h] ⓛ{p}W.U.
#a #h #G #L #V #T #H
elim (cnv_inv_appl_pred … H) -H #p #W #U #HV #HT #HVW #HTU
/3 width=7 by cpms_div, ex4_3_intro/
qed-.

lemma cnv_inv_cast_cpes (a) (h) (G) (L):
      ∀U,T. ⦃G,L⦄ ⊢ ⓝU.T ![a,h] →
      ∧∧ ⦃G,L⦄ ⊢ U ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] & ⦃G,L⦄ ⊢ U ⬌*[h,0,1] T.
#a #h #G #L #U #T #H
elim (cnv_inv_cast … H) -H
/3 width=3 by cpms_div, and3_intro/
qed-.

(* Eliminators with t-bound rt-equivalence for terms ************************)

lemma cnv_ind_cpes (a) (h) (Q:relation3 genv lenv term):
      (∀G,L,s. Q G L (⋆s)) →
      (∀I,G,K,V. ⦃G,K⦄ ⊢ V![a,h] → Q G K V → Q G (K.ⓑ{I}V) (#O)) →
      (∀I,G,K,i. ⦃G,K⦄ ⊢ #i![a,h] → Q G K (#i) → Q G (K.ⓘ{I}) (#(↑i))) →
      (∀p,I,G,L,V,T. ⦃G,L⦄ ⊢ V![a,h] → ⦃G,L.ⓑ{I}V⦄⊢T![a,h] →
                     Q G L V →Q G (L.ⓑ{I}V) T →Q G L (ⓑ{p,I}V.T)
      ) →
      (∀n,p,G,L,V,W,T,U. yinj n < a → ⦃G,L⦄ ⊢ V![a,h] → ⦃G,L⦄ ⊢ T![a,h] →
                         ⦃G,L⦄ ⊢ V ⬌*[h,1,0]W → ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W.U →
                         Q G L V → Q G L T → Q G L (ⓐV.T)
      ) →
      (∀G,L,U,T. ⦃G,L⦄⊢ U![a,h] → ⦃G,L⦄ ⊢ T![a,h] → ⦃G,L⦄ ⊢ U ⬌*[h,0,1] T →
                 Q G L U → Q G L T → Q G L (ⓝU.T)
      ) →
      ∀G,L,T. ⦃G,L⦄⊢ T![a,h] → Q G L T.
#a #h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #G #L #T #H
elim H -G -L -T [5,6: /3 width=7 by cpms_div/ |*: /2 width=1 by/ ]
qed-.
