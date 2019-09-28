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

include "basic_2/dynamic/nta_drops.ma".
include "basic_2/dynamic/nta_cpcs.ma".
include "basic_2/i_dynamic/ntas_cpcs.ma".
include "basic_2/i_dynamic/ntas_nta.ma".
include "basic_2/i_dynamic/ntas_ntas.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(* Advanced eliminators for native type assignment **************************)

lemma ntas_ind_bi_nta (h) (a) (G) (L) (Q:relation3 …):
      (∀T1,T2. ⦃G,L⦄ ⊢ T1 ![h,a] → ⦃G,L⦄ ⊢ T2 ![h,a] → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2 →
        Q 0 T1 T2
      ) →
      (∀T1,T2. ⦃G,L⦄ ⊢ T1 :[h,a] T2 → Q 1 T1 T2
      ) →
      (∀n1,n2,T1,T2,T0.  ⦃G,L⦄ ⊢ T1 :*[h,a,n1] T0 → ⦃G,L⦄ ⊢ T0 :*[h,a,n2] T2 →
        Q n1 T1 T0 → Q n2 T0 T2 → Q (n1+n2) T1 T2
      ) →
      ∀n,T1,T2. ⦃G,L⦄ ⊢ T1 :*[h,a,n] T2 → Q n T1 T2.
#h #a #G #L #Q #IH1 #IH2 #IH3 #n
@(nat_elim1 n) -n * [| * ]
[ #_ #T1 #T2 #H
  elim (ntas_inv_zero … H) -H #HT1 #HT2 #HT12
  /2 width=1 by/
| #_ #T1 #T2 #H
  /3 width=1 by ntas_inv_nta/
| #n #IH #T1 #T2 <plus_SO_sn #H
  elim (ntas_inv_plus … H) -H #T0 #HT10 #HT02
  /3 width=5 by/
]
qed-.

lemma nta_ind_cnv (h) (a) (Q:relation4 …):
      (∀G,L,s. Q G L (⋆s) (⋆(⫯[h]s))) →
      (∀G,K,V,W,U.
        ⦃G,K⦄ ⊢ V :[h,a] W → ⬆*[1] W ≘ U →
        Q G K V W → Q G (K.ⓓV) (#0) U
      ) →
      (∀G,K,W,U. ⦃G,K⦄ ⊢ W ![h,a] → ⬆*[1] W ≘ U → Q G (K.ⓛW) (#0) U) →
      (∀I,G,K,W,U,i.
        ⦃G,K⦄ ⊢ #i :[h,a] W → ⬆*[1] W ≘ U →
        Q G K (#i) W → Q G (K.ⓘ{I}) (#↑i) U
      ) →
      (∀p,I,G,K,V,T,U.
        ⦃G,K⦄ ⊢ V ![h,a] → ⦃G,K.ⓑ{I}V⦄ ⊢ T :[h,a] U →
        Q G (K.ⓑ{I}V) T U → Q G K (ⓑ{p,I}V.T) (ⓑ{p,I}V.U)
      ) →
      (∀p,G,L,V,W,T,U0,U. (**) (* one IH is missing *)
        ad a 0 → ⦃G,L⦄ ⊢ V :[h,a] W → ⦃G,L⦄ ⊢ T :*[h,a,0] ⓛ{p}W.U0 → ⦃G,L.ⓛW⦄ ⊢ U0 :[h,a] U →
        Q G L V W (* → Q G (L.ⓛW) U0 U *) → Q G L (ⓐV.T) (ⓐV.ⓛ{p}W.U)
      ) →
      (∀n,p,G,L,V,W,T,U,U0.
        ad a (↑n) → ⦃G,L⦄ ⊢ V :[h,a] W → ⦃G,L⦄ ⊢ T :[h,a] U → ⦃G,L⦄ ⊢ U :*[h,a,n] ⓛ{p}W.U0 →
        Q G L V W → Q G L T U → Q G L (ⓐV.T) (ⓐV.U)
      ) →
      (∀G,L,T,U. ⦃G,L⦄ ⊢ T :[h,a] U → Q G L T U → Q G L (ⓝU.T) U
      ) →
      (∀G,L,T,U1,U2.
        ⦃G,L⦄ ⊢ T :[h,a] U1 → ⦃G,L⦄ ⊢ U1 ⬌*[h] U2 → ⦃G,L⦄ ⊢ U2 ![h,a] →
        Q G L T U1 → Q G L T U2
      ) →
      ∀G,L,T,U. ⦃G,L⦄ ⊢ T :[h,a] U → Q G L T U.
#h #a #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #H9 #G #L #T
@(fqup_wf_ind_eq (Ⓣ) … G L T) -G -L -T #G0 #L0 #T0 #IH #G #L * * [|||| * ]
[ #s #HG #HL #HT #X #H destruct -IH
  elim (nta_inv_sort_sn … H) -H #HUX #HX
  /2 width=4 by/
| * [| #i ] #HG #HL #HT #X #H destruct
  [ elim (nta_inv_lref_sn_drops_cnv … H) -H *
    [ #K #V #W #U #H #HVW #HWU #HUX #HX
      lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
      /5 width=7 by nta_ldef, fqu_fqup, fqu_lref_O/
    | #K #W #U #H #HW #HWU #HUX #HX
      lapply (drops_fwd_isid … H ?) -H [ // ] #H destruct
      /3 width=4 by nta_ldec_cnv/
    ]
  | elim (nta_inv_lref_sn … H) -H #I #K #T #U #HT #HTU #HUX #HX #H destruct
    /5 width=7 by nta_lref, fqu_fqup/
  ]
| #l #HG #HL #HT #U #H destruct -IH
  elim (nta_inv_gref_sn … H)
| #p #I #V #T #HG #HL #HT #X #H destruct
  elim (nta_inv_bind_sn_cnv … H) -H #U #HV #HTU #HUX #HX
  /4 width=5 by nta_bind_cnv/
| #V #T #HG #HL #HT #X #H destruct
  elim (nta_inv_appl_sn_ntas … H) -H *
  [ #p #W #U #U0 #Ha #HVW #HTU0 #HU0 #HUX #HX -IH7
    /4 width=10 by nta_appl_ntas_zero/
  | #n #p #W #U #U0 #Ha #HVW #HTU #HU0 #HUX #HX -IH6
    /4 width=13 by nta_appl_ntas_pos/
  ]
| #U #T #HG #HL #HT #X #H destruct
  elim (nta_inv_cast_sn … H) -H #HTU #HUX #HX
  /4 width=4 by nta_cast/
]
qed-.
