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
include "basic_2/dynamic/nta_cpms.ma".
include "basic_2/dynamic/nta_cpcs.ma".
include "basic_2/dynamic/nta_preserve.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Advanced eliminators *****************************************************)

lemma nta_ind_rest_cnv (h) (Q:relation4 …):
      (∀G,L,s. Q G L (⋆s) (⋆(next h s))) →
      (∀G,K,V,W,U.
        ⦃G,K⦄ ⊢ V :[h] W → ⬆*[1] W ≘ U →
        Q G K V W → Q G (K.ⓓV) (#0) U
      ) →
      (∀G,K,W,U. ⦃G,K⦄ ⊢ W ![h] → ⬆*[1] W ≘ U → Q G (K.ⓛW) (#0) U) →
      (∀I,G,K,W,U,i.
        ⦃G,K⦄ ⊢ #i :[h] W → ⬆*[1] W ≘ U →
        Q G K (#i) W → Q G (K.ⓘ{I}) (#↑i) U
      ) →
      (∀p,I,G,K,V,T,U.
        ⦃G,K⦄ ⊢ V ![h] → ⦃G,K.ⓑ{I}V⦄ ⊢ T :[h] U →
        Q G (K.ⓑ{I}V) T U → Q G K (ⓑ{p,I}V.T) (ⓑ{p,I}V.U)
      ) →
      (∀p,G,L,V,W,T,U.
        ⦃G,L⦄ ⊢ V :[h] W → ⦃G,L⦄ ⊢ T :[h] ⓛ{p}W.U →
        Q G L V W → Q G L T (ⓛ{p}W.U) → Q G L (ⓐV.T) (ⓐV.ⓛ{p}W.U)
      ) →
      (∀G,L,T,U. ⦃G,L⦄ ⊢ T :[h] U → Q G L T U → Q G L (ⓝU.T) U
      ) →
      (∀G,L,T,U1,U2.
        ⦃G,L⦄ ⊢ T :[h] U1 → ⦃G,L⦄ ⊢ U1 ⬌*[h] U2 → ⦃G,L⦄ ⊢ U2 ![h] →
        Q G L T U1 → Q G L T U2
      ) →
      ∀G,L,T,U. ⦃G,L⦄ ⊢ T :[h] U → Q G L T U.
#h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #G #L #T
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
  elim (nta_inv_appl_sn … H) -H #p #W #U #HVW #HTU #HUX #HX
  /4 width=9 by nta_appl/
| #U #T #HG #HL #HT #X #H destruct
  elim (nta_inv_cast_sn … H) -H #HTU #HUX #HX
  /4 width=4 by nta_cast/
]
qed-.

lemma nta_ind_ext_cnv_mixed (h) (Q:relation4 …):
      (∀G,L,s. Q G L (⋆s) (⋆(next h s))) →
      (∀G,K,V,W,U.
        ⦃G,K⦄ ⊢ V :*[h] W → ⬆*[1] W ≘ U →
        Q G K V W → Q G (K.ⓓV) (#0) U
      ) →
      (∀G,K,W,U. ⦃G,K⦄ ⊢ W !*[h] → ⬆*[1] W ≘ U → Q G (K.ⓛW) (#0) U) →
      (∀I,G,K,W,U,i.
        ⦃G,K⦄ ⊢ #i :*[h] W → ⬆*[1] W ≘ U →
        Q G K (#i) W → Q G (K.ⓘ{I}) (#↑i) U
      ) →
      (∀p,I,G,K,V,T,U.
        ⦃G,K⦄ ⊢ V !*[h] → ⦃G,K.ⓑ{I}V⦄ ⊢ T :*[h] U →
        Q G (K.ⓑ{I}V) T U → Q G K (ⓑ{p,I}V.T) (ⓑ{p,I}V.U)
      ) →
      (∀p,G,L,V,W,T,U.
        ⦃G,L⦄ ⊢ V :*[h] W → ⦃G,L⦄ ⊢ T :*[h] ⓛ{p}W.U →
        Q G L V W → Q G L T (ⓛ{p}W.U) → Q G L (ⓐV.T) (ⓐV.ⓛ{p}W.U)
      ) →
      (∀G,L,V,T,U.
        ⦃G,L⦄ ⊢ T :*[h] U → ⦃G,L⦄ ⊢ ⓐV.U !*[h] →
        Q G L T U → Q G L (ⓐV.T) (ⓐV.U)
      ) →
      (∀G,L,T,U. ⦃G,L⦄ ⊢ T :*[h] U → Q G L T U → Q G L (ⓝU.T) U
      ) →
      (∀G,L,T,U1,U2.
        ⦃G,L⦄ ⊢ T :*[h] U1 → ⦃G,L⦄ ⊢ U1 ⬌*[h] U2 → ⦃G,L⦄ ⊢ U2 !*[h] →
        Q G L T U1 → Q G L T U2
      ) →
      ∀G,L,T,U. ⦃G,L⦄ ⊢ T :*[h] U → Q G L T U.
#h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #G #L #T
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
  elim (nta_inv_pure_sn_cnv … H) -H *
  [ #p #W #U #HVW #HTU #HUX #HX
    /4 width=9 by nta_appl/
  | #U #HTU #HVU #HUX #HX
    /4 width=6 by nta_pure_cnv/
  ]
| #U #T #HG #HL #HT #X #H destruct
  elim (nta_inv_cast_sn … H) -H #HTU #HUX #HX
  /4 width=4 by nta_cast/
]
qed-.

lemma nta_ind_ext_cnv (h) (Q:relation4 …):
      (∀G,L,s. Q G L (⋆s) (⋆(next h s))) →
      (∀G,K,V,W,U.
        ⦃G,K⦄ ⊢ V :*[h] W → ⬆*[1] W ≘ U →
        Q G K V W → Q G (K.ⓓV) (#0) U
      ) →
      (∀G,K,W,U. ⦃G,K⦄ ⊢ W !*[h] → ⬆*[1] W ≘ U → Q G (K.ⓛW) (#0) U) →
      (∀I,G,K,W,U,i.
        ⦃G,K⦄ ⊢ #i :*[h] W → ⬆*[1] W ≘ U →
        Q G K (#i) W → Q G (K.ⓘ{I}) (#↑i) U
      ) →
      (∀p,I,G,K,V,T,U.
        ⦃G,K⦄ ⊢ V !*[h] → ⦃G,K.ⓑ{I}V⦄ ⊢ T :*[h] U →
        Q G (K.ⓑ{I}V) T U → Q G K (ⓑ{p,I}V.T) (ⓑ{p,I}V.U)
      ) →
      (∀p,G,K,V,W,T,U.
        ⦃G,K⦄ ⊢ V :*[h] W → ⦃G,K.ⓛW⦄ ⊢ T :*[h] U →
        Q G K V W → Q G (K.ⓛW) T U → Q G K (ⓐV.ⓛ{p}W.T) (ⓐV.ⓛ{p}W.U)
      ) →
      (∀G,L,V,T,U.
        ⦃G,L⦄ ⊢ T :*[h] U → ⦃G,L⦄ ⊢ ⓐV.U !*[h] →
        Q G L T U → Q G L (ⓐV.T) (ⓐV.U)
      ) →
      (∀G,L,T,U. ⦃G,L⦄ ⊢ T :*[h] U → Q G L T U → Q G L (ⓝU.T) U
      ) →
      (∀G,L,T,U1,U2.
        ⦃G,L⦄ ⊢ T :*[h] U1 → ⦃G,L⦄ ⊢ U1 ⬌*[h] U2 → ⦃G,L⦄ ⊢ U2 !*[h] →
        Q G L T U1 → Q G L T U2
      ) →
      ∀G,L,T,U. ⦃G,L⦄ ⊢ T :*[h] U → Q G L T U.
#h #Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #G #L #T #U #H
@(nta_ind_ext_cnv_mixed … IH1 IH2 IH3 IH4 IH5 … IH7 IH8 IH9 … H) -G -L -T -U -IH1 -IH2 -IH3 -IH4 -IH5 -IH6 -IH8 -IH9
#p #G #L #V #W #T #U #HVW #HTU #_ #IHTU
lapply (nta_fwd_cnv_dx … HTU) #H
elim (cnv_inv_bind … H) -H #_ #HU
elim (cnv_nta_sn … HU) -HU #X #HUX
/4 width=2 by nta_appl_abst, nta_fwd_cnv_sn/
qed-.
