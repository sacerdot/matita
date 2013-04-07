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

include "basic_2/restricted/lpqs_cpqs.ma".

(* SN RESTRICTED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *****************)

(* Main properties **********************************************************)

theorem lpqs_conf: confluent … lpqs.
/3 width=6 by lpx_sn_conf, cpqs_conf_lpqs/
qed-.

theorem lpqs_trans: Transitive … lpqs.
/3 width=5 by lpx_sn_trans, cpqs_trans_lpqs/
qed-.

(* Advanced forward lemmas **************************************************)

lemma cpqs_fwd_shift1: ∀L1,L,T1,T. L ⊢ L1 @@ T1 ➤* T →
                       ∃∃L2,T2. L @@ L1 ⊢ ➤* L @@ L2 & L @@ L1 ⊢ T1 ➤* T2 &
                                T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1
[ #L #T1 #T #HT1
  @ex3_2_intro [3: // |4,5: // |1,2: skip ] (**) (* /2 width=4/ does not work *)
| #I #L1 #V1 #IH #L #T1 #T >shift_append_assoc #H <append_assoc
  elim (cpqs_inv_bind1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    elim (IH … HT12) -IH -HT12 #L2 #T #HL12 #HT1 #H destruct
    lapply (lpqs_trans … HL12 (L.ⓑ{I}V2@@L2) ?) -HL12 /3 width=1/ #HL12
    @(ex3_2_intro … (⋆.ⓑ{I}V2@@L2)) [4: /2 width=3/ | skip ] <append_assoc // (**) (* explicit constructor *)
  | #T #_ #_ #H destruct  
  ]
]
qed-.
