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

include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/reducibility/cpr_ltpss_sn.ma".
include "basic_2/reducibility/cfpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON CLOSURES *************************)

(* Advanced inversion lemmas ************************************************)

lemma cfpr_inv_pair1: ∀I,L,K1,L2,V1,T1,T2. L ⊢ ⦃⋆.ⓑ{I}V1@@K1, T1⦄ ➡ ⦃L2, T2⦄ →
                      ∃∃K2,V,V2. V1 ➡ V & L ⊢ V ▶* [0, |L|] V2 &
                                 L.ⓑ{I}V ⊢ ⦃K1, T1⦄ ➡ ⦃K2, T2⦄  &
                                 L2 = ⋆.ⓑ{I}V2@@K2.
* #L #K1 #L2 #V1 #T1 #T2 * >append_length #H
elim (length_inv_pos_sn_append … H) -H #I2 #K2 #V2 #HK12 #H destruct
>shift_append_assoc >shift_append_assoc normalize in ⊢ (??%%→?); #H
[ elim (cpr_inv_abbr1 … H) -H *
  [ #V #V0 #T0 #HV1 #HV0 #HT10 #H destruct /3 width=7/
  | #T0 #_ #_ #H destruct
  ]
| elim (cpr_inv_abst1 … H Abst V2) -H
  #V #T * #V0 #HV10 #HV0 #HT1 #H destruct
  lapply (ltpss_sn_cpr_trans (L.ⓛV0) … 0 (|L|+1) … HT1) -HT1 /2 width=1/ #HT12
  /3 width=7/
]
qed-.
