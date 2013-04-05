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

include "basic_2/unfold/lcpss_cpss.ma".

(* SN PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

(* Main properties **********************************************************)

theorem lcpss_conf: confluent … lcpss.
#L0 @(f_ind … length … L0) -L0 #n #IH *
[ #_ #X1 #H1 #X2 #H2 -n
  >(lcpss_inv_atom1 … H1) -X1
  >(lcpss_inv_atom1 … H2) -X2 /2 width=3/
| #L0 #I #V0 #Hn #X1 #H1 #X2 #H2 destruct
  elim (lcpss_inv_pair1 … H1) -H1 #L1 #V1 #HL01 #HV01 #H destruct
  elim (lcpss_inv_pair1 … H2) -H2 #L2 #V2 #HL02 #HV02 #H destruct
  elim (IH … HL01 … HL02) -IH normalize // #L #HL1 #HL2
  elim (cpss_conf_lcpss … HV01 … HV02 … HL01 … HL02) -L0 -V0 /3 width=5/
]
qed-.

theorem lcpss_trans: Transitive … lcpss.
#L1 #L #H elim H -L1 -L //
#I #L1 #L #V1 #V #HL1 #HV1 #IHL1 #X #H
elim (lcpss_inv_pair1 … H) -H #L2 #V2 #HL2 #HV2 #H destruct
lapply (cpss_trans_lcpss … HV1 … HL1 … HV2) -V -HL1 /3 width=1/
qed-.

(* Advanced forward lemmas **************************************************)

lemma cpss_fwd_shift1: ∀L1,L,T1,T. L ⊢ L1 @@ T1 ▶* T →
                       ∃∃L2,T2. L @@ L1 ⊢ ▶* L @@ L2 & L @@ L1 ⊢ T1 ▶* T2 &
                                T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1
[ #L #T1 #T #HT1
  @ex3_2_intro [3: // |4,5: // |1,2: skip ] (**) (* /2 width=4/ does not work *)
| #I #L1 #V1 #IH #L #T1 #T >shift_append_assoc #H <append_assoc
  elim (cpss_inv_bind1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IH … HT12) -IH -HT12 #L2 #T #HL12 #HT1 #H destruct
  lapply (lcpss_trans … HL12 (L.ⓑ{I}V2@@L2) ?) -HL12 /3 width=1/ #HL12
  @(ex3_2_intro … (⋆.ⓑ{I}V2@@L2)) [4: /2 width=3/ | skip ] <append_assoc // (**) (* explicit constructor *)
]
qed-.
