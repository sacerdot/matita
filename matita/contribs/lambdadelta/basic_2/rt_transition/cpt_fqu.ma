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

include "static_2/s_transition/fqu_weight.ma".
include "basic_2/rt_transition/cpt.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

(* Basic eliminators ********************************************************)

lemma cpt_ind (h) (Q:relation5 …):
      (∀I,G,L. Q 0 G L (⓪{I}) (⓪{I})) →
      (∀G,L,s. Q 1 G L (⋆s) (⋆(⫯[h]s))) →
      (∀n,G,K,V1,V2,W2. ⦃G,K⦄ ⊢ V1 ⬆[h,n] V2 → Q n G K V1 V2 →
        ⇧*[1] V2 ≘ W2 → Q n G (K.ⓓV1) (#0) W2
      ) → (∀n,G,K,V1,V2,W2. ⦃G,K⦄ ⊢ V1 ⬆[h,n] V2 → Q n G K V1 V2 →
        ⇧*[1] V2 ≘ W2 → Q (↑n) G (K.ⓛV1) (#0) W2
      ) → (∀n,I,G,K,T,U,i. ⦃G,K⦄ ⊢ #i ⬆[h,n] T → Q n G K (#i) T →
        ⇧*[1] T ≘ U → Q n G (K.ⓘ{I}) (#↑i) (U)
      ) → (∀n,p,I,G,L,V1,V2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬆[h,0] V2 → ⦃G,L.ⓑ{I}V1⦄ ⊢ T1 ⬆[h,n] T2 →
        Q 0 G L V1 V2 → Q n G (L.ⓑ{I}V1) T1 T2 → Q n G L (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
      ) → (∀n,G,L,V1,V2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬆[h,0] V2 → ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 →
        Q 0 G L V1 V2 → Q n G L T1 T2 → Q n G L (ⓐV1.T1) (ⓐV2.T2)
      ) → (∀n,G,L,V1,V2,T1,T2. ⦃G,L⦄ ⊢ V1 ⬆[h,n] V2 → ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 →
        Q n G L V1 V2 → Q n G L T1 T2 → Q n G L (ⓝV1.T1) (ⓝV2.T2)
      ) → (∀n,G,L,V1,V2,T. ⦃G,L⦄ ⊢ V1 ⬆[h,n] V2 →
        Q n G L V1 V2 → Q (↑n) G L (ⓝV1.T) V2
      ) →
      ∀n,G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ⬆[h,n] T2 → Q n G L T1 T2.
#h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #n #G #L #T1
generalize in match n; -n
@(fqu_wf_ind (Ⓣ) … G L T1) -G -L -T1 #G0 #L0 * [| * [| * ]]
[ #I #IH #n #X2 #HX2 -IH6 -IH7 -IH8 -IH9
  elim (cpt_inv_atom_sn … HX2) -HX2 *
  [ #H1 #H2 destruct -IH2 -IH3 -IH4 -IH5 //
  | #s #H1 #H2 #H3 destruct -IH1 -IH3 -IH4 -IH5 //
  | #K #V1 #V2 #HV12 #HVX2 #H1 #H2 destruct -IH1 -IH2 -IH4 -IH5 /3 width=4 by/
  | #m #K #W1 #W2 #HW12 #HWX2 #H1 #H2 #H3 destruct -IH1 -IH2 -IH3 -IH5 /3 width=4 by/
  | #J #K #T2 #i #HT2 #HTX2 #H1 #H2 destruct -IH1 -IH2 -IH3 -IH4 /3 width=4 by/
  ]
| #p #I #V1 #T1 #IH #n #X2 #HX2 -IH1 -IH2 -IH3 -IH4 -IH5 -IH7 -IH8 -IH9
  elim (cpt_inv_bind_sn … HX2) -HX2 #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=1 by fqu_bind_dx/
| #V1 #T1 #IH #n #X2 #HX2 -IH1 -IH2 -IH3 -IH4 -IH5 -IH6 -IH8 -IH9
  elim (cpt_inv_appl_sn … HX2) -HX2 #V2 #T2 #HV12 #HT12 #H destruct /3 width=1 by/
| #U1 #T1 #IH #n #X2 #HX2 -IH1 -IH2 -IH3 -IH4 -IH5 -IH6 -IH7
  elim (cpt_inv_cast_sn … HX2) -HX2 *
  [ #U2 #T2 #HU12 #HT12 #H destruct -IH9 /3 width=1 by/
  | #m #Hm #H destruct -IH8 /3 width=1 by/
  ]
]
qed-.
