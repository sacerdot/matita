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

include "basic_2/unfold/tpss_tpss.ma".
include "basic_2/unfold/delift.ma".

(* INVERSE BASIC TERM RELOCATION  *******************************************)

(* Main properties **********************************************************)

theorem delift_mono: ∀L,T,T1,T2,d,e.
                     L ⊢ ▼*[d, e] T ≡ T1 → L ⊢ ▼*[d, e] T ≡ T2 → T1 = T2.
#L #T #T1 #T2 #d #e * #U1 #H1TU1 #H2TU1 * #U2 #H1TU2 #H2TU2
elim (tpss_conf_eq … H1TU1 … H1TU2) -T #U #HU1 #HU2
lapply (tpss_inv_lift1_eq … HU1 … H2TU1) -HU1 #H destruct
lapply (tpss_inv_lift1_eq … HU2 … H2TU2) -HU2 #H destruct
lapply (lift_inj … H2TU1 … H2TU2) //
qed-.
