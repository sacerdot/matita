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

include "ground_2/ynat/ynat_lt.ma".
include "basic_2/notation/relations/exclaim_5.ma".
include "basic_2/notation/relations/exclaim_4.ma".
include "basic_2/notation/relations/exclaimstar_4.ma".
include "basic_2/rt_computation/cpms.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* activate genv *)
(* Basic_2A1: uses: snv *)
inductive cnv (a:ynat) (h): relation3 genv lenv term ≝
| cnv_sort: ∀G,L,s. cnv a h G L (⋆s)
| cnv_zero: ∀I,G,K,V. cnv a h G K V → cnv a h G (K.ⓑ{I}V) (#0)
| cnv_lref: ∀I,G,K,i. cnv a h G K (#i) → cnv a h G (K.ⓘ{I}) (#↑i)
| cnv_bind: ∀p,I,G,L,V,T. cnv a h G L V → cnv a h G (L.ⓑ{I}V) T → cnv a h G L (ⓑ{p,I}V.T)
| cnv_appl: ∀n,p,G,L,V,W0,T,U0. yinj n < a → cnv a h G L V → cnv a h G L T →
            ⦃G,L⦄ ⊢ V ➡*[1,h] W0 → ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W0.U0 → cnv a h G L (ⓐV.T)
| cnv_cast: ∀G,L,U,T,U0. cnv a h G L U → cnv a h G L T →
            ⦃G,L⦄ ⊢ U ➡*[h] U0 → ⦃G,L⦄ ⊢ T ➡*[1,h] U0 → cnv a h G L (ⓝU.T)
.

interpretation "context-sensitive native validity (term)"
   'Exclaim a h G L T = (cnv a h G L T).

interpretation "context-sensitive restricted native validity (term)"
   'Exclaim h G L T = (cnv (yinj (S (S O))) h G L T).

interpretation "context-sensitive extended native validity (term)"
   'ExclaimStar h G L T = (cnv Y h G L T).

(* Basic inversion lemmas ***************************************************)

fact cnv_inv_zero_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] → X = #0 →
                               ∃∃I,K,V. ⦃G,K⦄ ⊢ V ![a,h] & L = K.ⓑ{I}V.
#a #h #G #L #X * -G -L -X
[ #G #L #s #H destruct
| #I #G #K #V #HV #_ /2 width=5 by ex2_3_intro/
| #I #G #K #i #_ #H destruct
| #p #I #G #L #V #T #_ #_ #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #H destruct
]
qed-.

lemma cnv_inv_zero (a) (h): ∀G,L. ⦃G,L⦄ ⊢ #0 ![a,h] →
                            ∃∃I,K,V. ⦃G,K⦄ ⊢ V ![a,h] & L = K.ⓑ{I}V.
/2 width=3 by cnv_inv_zero_aux/ qed-.

fact cnv_inv_lref_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] → ∀i. X = #(↑i) →
                              ∃∃I,K. ⦃G,K⦄ ⊢ #i ![a,h] & L = K.ⓘ{I}.
#a #h #G #L #X * -G -L -X
[ #G #L #s #j #H destruct
| #I #G #K #V #_ #j #H destruct
| #I #G #L #i #Hi #j #H destruct /2 width=4 by ex2_2_intro/
| #p #I #G #L #V #T #_ #_ #j #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #j #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #j #H destruct
]
qed-.

lemma cnv_inv_lref (a) (h): ∀G,L,i. ⦃G,L⦄ ⊢ #↑i ![a,h] →
                            ∃∃I,K. ⦃G,K⦄ ⊢ #i ![a,h] & L = K.ⓘ{I}.
/2 width=3 by cnv_inv_lref_aux/ qed-.

fact cnv_inv_gref_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] → ∀l. X = §l → ⊥.
#a #h #G #L #X * -G -L -X
[ #G #L #s #l #H destruct
| #I #G #K #V #_ #l #H destruct
| #I #G #K #i #_ #l #H destruct
| #p #I #G #L #V #T #_ #_ #l #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #l #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #l #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_gref *)
lemma cnv_inv_gref (a) (h): ∀G,L,l. ⦃G,L⦄ ⊢ §l ![a,h] → ⊥.
/2 width=8 by cnv_inv_gref_aux/ qed-.

fact cnv_inv_bind_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] →
                               ∀p,I,V,T. X = ⓑ{p,I}V.T →
                               ∧∧ ⦃G,L⦄ ⊢ V ![a,h]
                                & ⦃G,L.ⓑ{I}V⦄ ⊢ T ![a,h].
#a #h #G #L #X * -G -L -X
[ #G #L #s #q #Z #X1 #X2 #H destruct
| #I #G #K #V #_ #q #Z #X1 #X2 #H destruct
| #I #G #K #i #_ #q #Z #X1 #X2 #H destruct
| #p #I #G #L #V #T #HV #HT #q #Z #X1 #X2 #H destruct /2 width=1 by conj/
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #q #Z #X1 #X2 #H destruct
| #G #L #U #T #U0 #_ #_ #_ #_ #q #Z #X1 #X2 #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_bind *)
lemma cnv_inv_bind (a) (h): ∀p,I,G,L,V,T. ⦃G,L⦄ ⊢ ⓑ{p,I}V.T ![a,h] →
                            ∧∧ ⦃G,L⦄ ⊢ V ![a,h]
                             & ⦃G,L.ⓑ{I}V⦄ ⊢ T ![a,h].
/2 width=4 by cnv_inv_bind_aux/ qed-.

fact cnv_inv_appl_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] → ∀V,T. X = ⓐV.T →
                               ∃∃n,p,W0,U0. yinj n < a & ⦃G,L⦄ ⊢ V ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
                                            ⦃G,L⦄ ⊢ V ➡*[1,h] W0 & ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W0.U0.
#a #h #G #L #X * -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #K #V #_ #X1 #X2 #H destruct
| #I #G #K #i #_ #X1 #X2 #H destruct
| #p #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #n #p #G #L #V #W0 #T #U0 #Ha #HV #HT #HVW0 #HTU0 #X1 #X2 #H destruct /3 width=7 by ex5_4_intro/
| #G #L #U #T #U0 #_ #_ #_ #_ #X1 #X2 #H destruct
]
qed-.

(* Basic_2A1: uses: snv_inv_appl *)
lemma cnv_inv_appl (a) (h): ∀G,L,V,T. ⦃G,L⦄ ⊢ ⓐV.T ![a,h] →
                            ∃∃n,p,W0,U0. yinj n < a & ⦃G,L⦄ ⊢ V ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
                                         ⦃G,L⦄ ⊢ V ➡*[1,h] W0 & ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W0.U0.
/2 width=3 by cnv_inv_appl_aux/ qed-.

fact cnv_inv_cast_aux (a) (h): ∀G,L,X. ⦃G,L⦄ ⊢ X ![a,h] → ∀U,T. X = ⓝU.T →
                               ∃∃U0. ⦃G,L⦄ ⊢ U ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
                                     ⦃G,L⦄ ⊢ U ➡*[h] U0 & ⦃G,L⦄ ⊢ T ➡*[1,h] U0.
#a #h #G #L #X * -G -L -X
[ #G #L #s #X1 #X2 #H destruct
| #I #G #K #V #_ #X1 #X2 #H destruct
| #I #G #K #i #_ #X1 #X2 #H destruct
| #p #I #G #L #V #T #_ #_ #X1 #X2 #H destruct
| #n #p #G #L #V #W0 #T #U0 #_ #_ #_ #_ #_ #X1 #X2 #H destruct
| #G #L #U #T #U0 #HV #HT #HU0 #HTU0 #X1 #X2 #H destruct /2 width=3 by ex4_intro/
]
qed-.

(* Basic_2A1: uses: snv_inv_appl *)
lemma cnv_inv_cast (a) (h): ∀G,L,U,T. ⦃G,L⦄ ⊢ ⓝU.T ![a,h] →
                            ∃∃U0. ⦃G,L⦄ ⊢ U ![a,h] & ⦃G,L⦄ ⊢ T ![a,h] &
                                  ⦃G,L⦄ ⊢ U ➡*[h] U0 & ⦃G,L⦄ ⊢ T ➡*[1,h] U0.
/2 width=3 by cnv_inv_cast_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma cnv_fwd_flat (a) (h) (I) (G) (L):
                   ∀V,T. ⦃G,L⦄ ⊢ ⓕ{I}V.T ![a,h] →
                   ∧∧ ⦃G,L⦄ ⊢ V ![a,h] & ⦃G,L⦄ ⊢ T ![a,h].
#a #h * #G #L #V #T #H
[ elim (cnv_inv_appl … H) #n #p #W #U #_ #HV #HT #_ #_
| elim (cnv_inv_cast … H) #U #HV #HT #_ #_
] -H /2 width=1 by conj/
qed-.

lemma cnv_fwd_pair_sn (a) (h) (I) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ②{I}V.T ![a,h] → ⦃G,L⦄ ⊢ V ![a,h].
#a #h * [ #p ] #I #G #L #V #T #H
[ elim (cnv_inv_bind … H) -H #HV #_
| elim (cnv_fwd_flat … H) -H #HV #_
] //
qed-.

(* Basic_2A1: removed theorems 3:
              shnv_cast shnv_inv_cast snv_shnv_cast
*)
