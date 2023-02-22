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

include "basic_2/rt_transition/cpg_drops.ma".
include "basic_2/rt_transition/cpt_fqu.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

(* Properties with generic slicing for local environments *******************)

lemma cpt_lifts_sn (h) (n) (G):
      d_liftable2_sn … lifts (λL. cpt h G L n).
#h #n #G #K #T1 #T2 * #c #Hc #HT12 #b #f #L #HLK #U1 #HTU1
elim (cpg_lifts_sn … HT12 … HLK … HTU1) -K -T1
/3 width=5 by ex2_intro/
qed-.

lemma cpt_lifts_bi (h) (n) (G):
      d_liftable2_bi … lifts (λL. cpt h G L n).
#h #n #G #K #T1 #T2 * /3 width=11 by cpg_lifts_bi, ex2_intro/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma cpt_inv_lifts_sn (h) (n) (G):
      d_deliftable2_sn … lifts (λL. cpt h G L n).
#h #n #G #L #U1 #U2 * #c #Hc #HU12 #b #f #K #HLK #T1 #HTU1
elim (cpg_inv_lifts_sn … HU12 … HLK … HTU1) -L -U1
/3 width=5 by ex2_intro/
qed-.

lemma cpt_inv_lifts_bi (h) (n) (G):
      d_deliftable2_bi … lifts (λL. cpt h G L n).
#h #n #G #L #U1 #U2 * /3 width=11 by cpg_inv_lifts_bi, ex2_intro/
qed-.

(* Advanced properties ******************************************************)

lemma cpt_delta_drops (h) (n) (G):
      ∀L,K,V,i. ⇩[i] L ≘ K.ⓓV → ∀V2. ❨G,K❩ ⊢ V ⬆[h,n] V2 →
      ∀W2. ⇧[↑i] V2 ≘ W2 → ❨G,L❩ ⊢ #i ⬆[h,n] W2.
#h #n #G #L #K #V #i #HLK #V2 *
/3 width=8 by cpg_delta_drops, ex2_intro/
qed.

lemma cpt_ell_drops (h) (n) (G):
      ∀L,K,V,i. ⇩[i] L ≘ K.ⓛV → ∀V2. ❨G,K❩ ⊢ V ⬆[h,n] V2 →
      ∀W2. ⇧[↑i] V2 ≘ W2 → ❨G,L❩ ⊢ #i ⬆[h,↑n] W2.
#h #n #G #L #K #V #i #HLK #V2 *
/3 width=8 by cpg_ell_drops, ist_succ, ex2_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpt_inv_atom_sn_drops (h) (n) (I) (G) (L):
      ∀X2. ❨G,L❩ ⊢ ⓪[I] ⬆[h,n] X2 →
      ∨∨ ∧∧ X2 = ⓪[I] & n = 0
       | ∃∃s. X2 = ⋆(⫯[h]s) & I = Sort s & n = 1
       | ∃∃K,V,V2,i. ⇩[i] L ≘ K.ⓓV & ❨G,K❩ ⊢ V ⬆[h,n] V2 & ⇧[↑i] V2 ≘ X2 & I = LRef i
       | ∃∃m,K,V,V2,i. ⇩[i] L ≘ K.ⓛV & ❨G,K❩ ⊢ V ⬆[h,m] V2 & ⇧[↑i] V2 ≘ X2 & I = LRef i & n = ↑m.
#h #n #I #G #L #X2 * #c #Hc #H elim (cpg_inv_atom1_drops … H) -H *
[ #H1 #H2 destruct
  /3 width=1 by or4_intro0, conj/
| #s1 #s2 #H1 #H2 #H3 #H4 destruct
  /3 width=3 by or4_intro1, ex3_intro/
| #cV #i #K #V1 #V2 #HLK #HV12 #HVT2 #H1 #H2 destruct
  /4 width=8 by ex4_4_intro, ex2_intro, or4_intro2/
| #cV #i #K #V1 #V2 #HLK #HV12 #HVT2 #H1 #H2 destruct
  elim (ist_inv_plus_SO_dx … H2) -H2
  /4 width=10 by ex5_5_intro, ex2_intro, or4_intro3/
]
qed-.

lemma cpt_inv_lref_sn_drops (h) (n) (G) (L) (i):
      ∀X2. ❨G,L❩ ⊢ #i ⬆[h,n] X2 →
      ∨∨ ∧∧ X2 = #i & n = 0
       | ∃∃K,V,V2. ⇩[i] L ≘ K.ⓓV & ❨G,K❩ ⊢ V ⬆[h,n] V2 & ⇧[↑i] V2 ≘ X2
       | ∃∃m,K,V,V2. ⇩[i] L ≘ K. ⓛV & ❨G,K❩ ⊢ V ⬆[h,m] V2 & ⇧[↑i] V2 ≘ X2 & n = ↑m.
#h #n #G #L #i #X2 * #c #Hc #H elim (cpg_inv_lref1_drops … H) -H *
[ #H1 #H2 destruct
  /3 width=1 by or3_intro0, conj/
| #cV #K #V1 #V2 #HLK #HV12 #HVT2 #H destruct
  /4 width=6 by ex3_3_intro, ex2_intro, or3_intro1/
| #cV #K #V1 #V2 #HLK #HV12 #HVT2 #H destruct
  elim (ist_inv_plus_SO_dx … H) -H
  /4 width=8 by ex4_4_intro, ex2_intro, or3_intro2/
]
qed-.

(* Advanced forward lemmas **************************************************)

fact cpt_fwd_plus_aux (h) (n) (G) (L):
     ∀T1,T2. ❨G,L❩ ⊢ T1 ⬆[h,n] T2 → ∀n1,n2. n1+n2 = n →
     ∃∃T. ❨G,L❩ ⊢ T1 ⬆[h,n1] T & ❨G,L❩ ⊢ T ⬆[h,n2] T2.
#h #n #G #L #T1 #T2 #H @(cpt_ind … H) -G -L -T1 -T2 -n
[ #I #G #L #n1 #n2 #H
  elim (plus_inv_O3 … H) -H #H1 #H2 destruct
  /2 width=3 by ex2_intro/
| #G #L #s #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct /2 width=3 by ex2_intro/
  | #n1 #H1 #H elim (plus_inv_O3 … H) -H #H2 #H3 destruct
    /2 width=3 by ex2_intro/
  ]
| #n #G #K #V1 #V2 #W2 #_ #IH #HVW2 #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #V #HV1 #HV2
  elim (lifts_total V 𝐔❨↑O❩) #W #HVW
  /5 width=11 by cpt_lifts_bi, cpt_delta, drops_refl, drops_drop, ex2_intro/
| #n #G #K #V1 #V2 #W2 #HV12 #IH #HVW2 #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct -IH /3 width=3 by cpt_ell, ex2_intro/
  | #n1 #H1 #H2 destruct -HV12
    elim (IH n1) [|*: // ] -IH #V #HV1 #HV2
    elim (lifts_total V 𝐔❨↑O❩) #W #HVW
    /5 width=11 by cpt_lifts_bi, cpt_ell, drops_refl, drops_drop, ex2_intro/
  ]
| #n #I #G #K #T2 #U2 #i #_ #IH #HTU2 #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  elim (lifts_total T 𝐔❨↑O❩) #U #HTU
  /5 width=11 by cpt_lifts_bi, cpt_lref, drops_refl, drops_drop, ex2_intro/
| #n #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ #IHT #n1 #n2 #H destruct
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpt_bind, ex2_intro/
| #n #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ #IHT #n1 #n2 #H destruct
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpt_appl, ex2_intro/
| #n #G #L #U1 #U2 #T1 #T2 #_ #_ #IHU #IHT #n1 #n2 #H destruct
  elim IHU [|*: // ] -IHU #U #HU1 #HU2
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpt_cast, ex2_intro/
| #n #G #L #U1 #U2 #T #HU12 #IH #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct -IH /3 width=4 by cpt_ee, cpt_cast, ex2_intro/
  | #n1 #H1 #H2 destruct -HU12
    elim (IH n1) [|*: // ] -IH #U #HU1 #HU2
    /3 width=3 by cpt_ee, ex2_intro/
  ]
]
qed-.

lemma cpt_fwd_plus (h) (n1) (n2) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ⬆[h,n1+n2] T2 →
      ∃∃T. ❨G,L❩ ⊢ T1 ⬆[h,n1] T & ❨G,L❩ ⊢ T ⬆[h,n2] T2.
/2 width=3 by cpt_fwd_plus_aux/ qed-.
