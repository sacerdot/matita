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

include "basic_2/reducibility/tpr_tpr.ma".
include "basic_2/reducibility/ltpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Main properties **********************************************************)

theorem ltpr_conf: ∀L0:lenv. ∀L1. L0 ➡ L1 → ∀L2. L0 ➡ L2 →
                   ∃∃L. L1 ➡ L & L2 ➡ L.
#L0 #L1 #H elim H -L0 -L1 /2 width=3/
#I #K0 #K1 #V0 #V1 #_ #HV01 #IHK01 #L2 #H
elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK02 #HV02 #H destruct
elim (IHK01 … HK02) -K0 #K #HK1 #HK2
elim (tpr_conf … HV01 HV02) -V0 /3 width=5/
qed.
