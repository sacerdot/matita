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

include "basic_2/unfold/tpss_alt.ma".
include "basic_2/unfold/ltpss_ltpss.ma".
include "basic_2/unfold/delift_alt.ma".
include "basic_2/unfold/thin.ma".

(* DELIFT ON LOCAL ENVIRONMENTS *********************************************)

(* Properties on deflift on terms *******************************************)

lemma thin_delift1: ∀L1,L2,d,e. L1 [d, e] ≡ L2 → ∀V1,V2. L1 ⊢ V1 [d, e] ≡ V2 →
                    ∀I. L1.ⓑ{I}V1 [d + 1, e] ≡ L2.ⓑ{I}V2.
#L1 #L2 #d #e * #L #HL1 #HL2 #V1 #V2 * #V #HV1 #HV2 #I
elim (ltpss_tpss_conf … HV1 … HL1) -HV1 #V0 #HV10 #HV0
elim (tpss_inv_lift1_be … HV0 … HL2 … HV2 ? ?) -HV0 // <minus_n_n #X #H1 #H2
lapply (tpss_inv_refl_O2 … H1) -H1 #H destruct
lapply (lift_mono … H2 … HV2) -H2 #H destruct /3 width=5/
qed.

axiom delift_tpss_conf_be: ∀L,U1,U2,d,e. L ⊢ U1 [d, e] ▶* U2 →
                           ∀T1,dd,ee. L ⊢ U1 [dd, ee] ≡ T1 → ∀K. L [dd, ee] ≡ K →
                           d ≤ dd → dd + ee ≤ d + e →
                           ∃∃T2. K ⊢ T1 [dd - d, e - ee] ▶* T2 & L ⊢ U2 [dd, ee] ≡ T2.
(*
#L #U1 #U2 #d #e #H @(tpss_ind_alt … H) -L -U1 -U2 -d -e
[ #L * #i #d #e #X #dd #ee #H
  [ >(delift_inv_sort1 … H) -X /2 width=3/
  | elim (delift_inv_lref1 … H) -H * [1,3: /3 width=3/ | /3 width=6/ ]
  | >(delift_inv_gref1 … H) -X /2 width=3/
  ]
| #L #K1 #V1 #V2 #W2 #i #d #e #Hdi #Hide #HLK1 #_ #HVW2 #IHV12 #T1 #dd #ee #H #K2 #HLK2 #Hdd #Hddee
  lapply 
    
    @(ex2_1_intro … X) // /2 width=6/
*)
