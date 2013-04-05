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

notation "hvbox( T1 break ⊢ ▶ ▶ * [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarSnAlt $T1 $d $e $T2 }.

include "basic_2/unfold/ltpss_dx_ltpss_dx.ma".
include "basic_2/unfold/ltpss_sn_ltpss_sn.ma".

(* SN PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

(* alternative definition of ltpss_sn *)
definition ltpssa: nat → nat → relation lenv ≝
                   λd,e. TC … (ltpss_dx d e).

interpretation "parallel unfold (local environment, sn variant) alternative"
   'PSubstStarSnAlt L1 d e L2 = (ltpssa d e L1 L2).

(* Basic eliminators ********************************************************)

lemma ltpssa_ind: ∀d,e,L1. ∀R:predicate lenv. R L1 →
                  (∀L,L2. L1 ⊢ ▶▶* [d, e] L → L ▶* [d, e] L2 → R L → R L2) →
                  ∀L2. L1 ⊢ ▶▶* [d, e] L2 → R L2.
#d #e #L1 #R #HL1 #IHL1 #L2 #HL12 @(TC_star_ind … HL1 IHL1 … HL12) //
qed-.

lemma ltpssa_ind_dx: ∀d,e,L2. ∀R:predicate lenv. R L2 →
                     (∀L1,L. L1 ▶* [d, e] L → L ⊢ ▶▶* [d, e] L2 → R L → R L1) →
                     ∀L1. L1 ⊢ ▶▶* [d, e] L2 → R L1.
#d #e #L2 #R #HL2 #IHL2 #L1 #HL12 @(TC_star_ind_dx … HL2 IHL2 … HL12) //
qed-.

(* Basic properties *********************************************************)

lemma ltpssa_refl: ∀L,d,e. L ⊢ ▶▶* [d, e] L.
/2 width=1/ qed.

lemma ltpssa_tpss2: ∀I,L1,V1,V2,e. L1 ⊢ V1 ▶*[0, e] V2 →
                    ∀L2. L1 ⊢ ▶▶* [0, e] L2 →
                    L1.ⓑ{I}V1 ⊢ ▶▶* [O, e + 1] L2.ⓑ{I}V2.
#I #L1 #V1 #V2 #e #HV12 #L2 #H @(ltpssa_ind … H) -L2
[ /3 width=1/ | /3 width=5/ ]
qed.

lemma ltpssa_tpss1: ∀I,L1,V1,V2,d,e. L1 ⊢ V1 ▶*[d, e] V2 →
                    ∀L2. L1 ⊢ ▶▶* [d, e] L2 →
                    L1.ⓑ{I}V1 ⊢ ▶▶* [d + 1, e] L2.ⓑ{I}V2.
#I #L1 #V1 #V2 #d #e #HV12 #L2 #H @(ltpssa_ind … H) -L2
[ /3 width=1/ | /3 width=5/ ]
qed.

lemma ltpss_sn_ltpssa: ∀L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 → L1 ⊢ ▶▶* [d, e] L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e // /2 width=1/
qed.

lemma ltpss_sn_dx_trans_eq: ∀L1,L,d,e. L1 ⊢ ▶* [d, e] L →
                            ∀L2. L ▶* [d, e] L2 → L1 ⊢ ▶* [d, e] L2.
#L1 #L #d #e #H elim H -L1 -L -d -e
[ #d #e #X #H
  lapply (ltpss_dx_inv_atom1 … H) -H #H destruct //
| #L #I #V #X #H
  lapply (ltpss_dx_inv_refl_O2 … H) -H #H destruct //
| #L1 #L #I #V1 #V #e #_ #HV1 #IHL1 #X #H
  elim (ltpss_dx_inv_tpss21 … H ?) -H // <minus_plus_m_m
  #L2 #V2 #HL2 #HV2 #H destruct
  lapply (IHL1 … HL2) -L #HL12
  lapply (ltpss_sn_tpss_trans_eq … HV2 … HL12) -HV2 #HV2
  lapply (tpss_trans_eq … HV1 HV2) -V /2 width=1/
| #L1 #L #I #V1 #V #d #e #_ #HV1 #IHL1 #X #H
  elim (ltpss_dx_inv_tpss11 … H ?) -H // <minus_plus_m_m
  #L2 #V2 #HL2 #HV2 #H destruct
  lapply (IHL1 … HL2) -L #HL12
  lapply (ltpss_sn_tpss_trans_eq … HV2 … HL12) -HV2 #HV2
  lapply (tpss_trans_eq … HV1 HV2) -V /2 width=1/
]
qed.

lemma ltpss_dx_sn_trans_eq: ∀L1,L,d,e. L1 ▶* [d, e] L →
                            ∀L2. L ⊢ ▶* [d, e] L2 → L1 ⊢ ▶* [d, e] L2.
/3 width=3/ qed.

lemma ltpssa_strip: ∀L0,L1,d1,e1. L0 ⊢ ▶▶* [d1, e1] L1 →
                    ∀L2,d2,e2. L0 ▶* [d2, e2] L2 →
                    ∃∃L. L1 ▶* [d2, e2] L & L2 ⊢ ▶▶* [d1, e1] L.
/3 width=3/ qed.

(* Basic inversion lemmas ***************************************************)

lemma ltpssa_ltpss_sn: ∀L1,L2,d,e. L1 ⊢ ▶▶* [d, e] L2 → L1 ⊢ ▶* [d, e] L2.
#L1 #L2 #d #e #H @(ltpssa_ind … H) -L2 // /2 width=3/
qed-.

(* Advanced properties ******************************************************)

lemma ltpss_sn_strip: ∀L0,L1,d1,e1. L0 ⊢ ▶* [d1, e1] L1 →
                      ∀L2,d2,e2. L0 ▶* [d2, e2] L2 →
                      ∃∃L. L1 ▶* [d2, e2] L & L2 ⊢ ▶* [d1, e1] L.
#L0 #L1 #d1 #e1 #H #L2 #d2 #e2 #HL02
lapply (ltpss_sn_ltpssa … H) -H #HL01
elim (ltpssa_strip … HL01 … HL02) -L0
/3 width=3 by ltpssa_ltpss_sn, ex2_intro/
qed.

(* Note: this should go in ltpss_sn_ltpss_sn.ma *)
lemma ltpss_sn_tpss_conf: ∀L0,T2,U2,d2,e2. L0 ⊢ T2 ▶* [d2, e2] U2 →
                          ∀L1,d1,e1. L0 ⊢ ▶* [d1, e1] L1 →
                          ∃∃T. L1 ⊢ T2 ▶* [d2, e2] T &
                               L0 ⊢ U2 ▶* [d1, e1] T.
#L0 #T2 #U2 #d2 #e2 #HTU2 #L1 #d1 #e1 #H
lapply (ltpss_sn_ltpssa … H) -H #H @(ltpssa_ind … H) -L1 /2 width=3/ -HTU2
#L #L1 #H #HL1 * #T #HT2 #HU2T
lapply (ltpssa_ltpss_sn … H) -H #HL0
lapply (ltpss_sn_dx_trans_eq … HL0 … HL1) -HL0 #HL01
elim (ltpss_dx_tpss_conf … HT2 … HL1) -HT2 -HL1 #T0 #HT20 #HT0
lapply (ltpss_sn_tpss_trans_eq … HT0 … HL01) -HT0 -HL01 #HT0
lapply (tpss_trans_eq … HU2T HT0) -T /2 width=3/
qed.

(* Note: this should go in ltpss_sn_ltpss_sn.ma *)
lemma ltpss_sn_tpss_trans_down: ∀L0,L1,T2,U2,d1,e1,d2,e2. d2 + e2 ≤ d1 →
                                L1 ⊢ ▶* [d1, e1] L0 → L0 ⊢ T2 ▶* [d2, e2] U2 →
                                ∃∃T. L1 ⊢ T2 ▶* [d2, e2] T & L1 ⊢ T ▶* [d1, e1] U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde2d1 #H #HTU2
lapply (ltpss_sn_ltpssa … H) -H #HL10
@(ltpssa_ind_dx … HL10) -L1 /2 width=3/ -HTU2
#L1 #L #HL1 #_ * #T #HT2 #HTU2
elim (ltpss_dx_tpss_trans_down … HL1 HT2) -HT2 // #T0 #HT20 #HT0 -Hde2d1
lapply (tpss_trans_eq … HT0 HTU2) -T #HT0U2
lapply (ltpss_dx_tpss_trans_eq … HT0U2 … HL1) -HT0U2 -HL1 /2 width=3/
qed.

(* Main properties **********************************************************)

theorem ltpssa_conf: ∀L0,L1,d1,e1. L0 ⊢ ▶▶* [d1, e1] L1 →
                     ∀L2,d2,e2. L0 ⊢ ▶▶* [d2, e2] L2 →
                     ∃∃L. L1 ⊢ ▶▶* [d2, e2] L & L2 ⊢ ▶▶* [d1, e1] L.
/3 width=3/ qed.

(* Note: this should go in ltpss_sn_ltpss_sn.ma *)
theorem ltpss_sn_conf: ∀L0,L1,d1,e1. L0 ⊢ ▶* [d1, e1] L1 →
                       ∀L2,d2,e2. L0 ⊢ ▶* [d2, e2] L2 →
                       ∃∃L. L1 ⊢ ▶* [d2, e2] L & L2 ⊢ ▶* [d1, e1] L.
#L0 #L1 #d1 #e1 #H1 #L2 #d2 #e2 #H2
lapply (ltpss_sn_ltpssa … H1) -H1 #HL01
lapply (ltpss_sn_ltpssa … H2) -H2 #HL02
elim (ltpssa_conf … HL01 … HL02) -L0
/3 width=3 by ltpssa_ltpss_sn, ex2_intro/
qed.
