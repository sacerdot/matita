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
(*
include "basic_2/multiple/frees_lreq.ma".
include "basic_2/multiple/frees_lift.ma".
*)
include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/lfpx.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with context-sensitive free variables ***************************)

lemma lpx_cpx_frees_fwd_sge: ∀h,G,L1,U1,U2. ⦃G, L1⦄ ⊢ U1 ⬈[h] U2 →
                             ∀L2. ⦃G, L1⦄ ⊢ ⬈[h, U1] L2 →
                             ∀g1. L1 ⊢ 𝐅*⦃U1⦄ ≡ g1 → ∀g2. L2 ⊢ 𝐅*⦃U2⦄ ≡ g2 →
                             g2 ⊆ g1.
#h #G #L1 #U1 @(fqup_wf_ind_eq … G L1 U1) -G -L1 -U1
#G0 #L0 #U0 #IH #G #L1 * *
[ #s #HG #HL #HU #U2 #H0 #L2 #_ #g1 #H1 #g2 #H2 -IH -G0 -L0 -U0
  elim (cpx_inv_sort1 … H0) -H0 #H destruct
  /3 width=3 by frees_inv_sort, sle_isid_sn/
| #i #HG #HL #HU #U2 #H0 #L2 #HL12 #g1 #H1 #g2 #H2 destruct
  elim (cpx_inv_lref1_drops … H0) -H0
  [ #H destruct
    lapply (frees_inv_lref … H1) -H1 #Hg1
    lapply (frees_inv_sort … H2) -H2 #Hg2 /2 width=1 by sle_isid_sn/  



| #l #HG #HL #HU #U2 #H0 #L2 #_ #g1 #H1 #g2 #H2 -IH -G0 -L0 -U0
  lapply (cpx_inv_gref1 … H0) -H0 #H destruct
  /3 width=3 by frees_inv_gref, sle_isid_sn/
  
| #j #HG #HL #HU #U2 #H1 #L2 #HL12 #i #H2 elim (cpx_inv_lref1 … H1) -H1
  [ #H destruct elim (frees_inv_lref … H2) -H2 //
    * #I #K2 #W2 #Hj #Hji #HLK2 #HW2
    elim (lpx_drop_trans_O1 … HL12 … HLK2) -HL12 #Y #HLK1 #H
    elim (lpx_inv_pair2 … H) -H #K1 #W1 #HK12 #HW12 #H destruct
    /4 width=11 by frees_lref_be, fqup_lref/
  | * #I #K1 #W1 #W0 #HLK1 #HW10 #HW0U2
    lapply (drop_fwd_drop2 … HLK1) #H0
    elim (lpx_drop_conf … H0 … HL12) -H0 -HL12 #K2 #HK12 #HLK2
    elim (ylt_split i (j+1)) >yplus_SO2 #Hji
    [ -IH elim (frees_inv_lift_be … H2 … HLK2 … HW0U2) /2 width=1 by ylt_fwd_succ2/
    | lapply (frees_inv_lift_ge … H2 … HLK2 … HW0U2 ?) -L2 -U2 // destruct
      /4 width=11 by frees_lref_be, fqup_lref, yle_succ1_inj/
    ]
  ]
| -IH #p #HG #HL #HU #U2 #H1 >(cpx_inv_gref1 … H1) -H1 destruct
   #L2 #_ #i #H2 elim (frees_inv_gref … H2)
| #a #I #W1 #U1 #HG #HL #HU #X #HX #L2 #HL12 #i #Hi destruct
  elim (cpx_inv_bind1 … HX) -HX *
  [ #W2 #U2 #HW12 #HU12 #H destruct
    elim (frees_inv_bind_O … Hi) -Hi
    /4 width=7 by frees_bind_dx_O, frees_bind_sn, lpx_pair/
  | #U2 #HU12 #HXU2 #H1 #H2 destruct
    lapply (frees_lift_ge … Hi (L2.ⓓW1) (Ⓕ) … HXU2 ?)
    /4 width=7 by frees_bind_dx_O, lpx_pair, drop_drop/
  ]
| #I #W1 #X1 #HG #HL #HU #X2 #HX2 #L2 #HL12 #i #Hi destruct
  elim (cpx_inv_flat1 … HX2) -HX2 *
  [ #W2 #U2 #HW12 #HU12 #H destruct
    elim (frees_inv_flat … Hi) -Hi /3 width=7 by frees_flat_dx, frees_flat_sn/
  | #HU12 #H destruct /3 width=7 by frees_flat_dx/
  | #HW12 #H destruct /3 width=7 by frees_flat_sn/
  | #b #W2 #V1 #V2 #U1 #U2 #HW12 #HV12 #HU12 #H1 #H2 #H3 destruct
    elim (frees_inv_bind … Hi) -Hi #Hi
    [ elim (frees_inv_flat … Hi) -Hi
      /4 width=7 by frees_flat_dx, frees_flat_sn, frees_bind_sn/
    | lapply (lreq_frees_trans … Hi (L2.ⓛV2) ?) /2 width=1 by lreq_succ/ -Hi #HU2
      lapply (frees_weak … HU2 0 ?) -HU2
      /5 width=7 by frees_bind_dx_O, frees_flat_dx, lpx_pair/
    ]
  | #b #W2 #W0 #V1 #V2 #U1 #U2 #HW12 #HW20 #HV12 #HU12 #H1 #H2 #H3 destruct
    elim (frees_inv_bind_O … Hi) -Hi #Hi
    [ /4 width=7 by frees_flat_dx, frees_bind_sn/
    | elim (frees_inv_flat … Hi) -Hi
      [ #HW0 lapply (frees_inv_lift_ge … HW0 L2 (Ⓕ) … HW20 ?) -W0
        /3 width=7 by frees_flat_sn, drop_drop/
      | /5 width=7 by frees_bind_dx_O, frees_flat_dx, lpx_pair/
      ]
    ]
  ]
]
qed-.

lemma cpx_frees_trans: ∀h,o,G. frees_trans (cpx h o G).
/2 width=8 by lpx_cpx_frees_trans/ qed-.

lemma lpx_frees_trans: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 →
                       ∀U,i. L2 ⊢ i ϵ 𝐅*[0]⦃U⦄ → L1 ⊢ i ϵ 𝐅*[0]⦃U⦄.
/2 width=8 by lpx_cpx_frees_trans/ qed-.
