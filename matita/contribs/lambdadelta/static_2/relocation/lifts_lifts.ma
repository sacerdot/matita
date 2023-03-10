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

include "static_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Main properties **********************************************************)

(* Basic_1: includes: lift_gen_lift *)
(* Basic_2A1: includes: lift_div_le lift_div_be *)
theorem lifts_div4: ∀f2,Tf,T. ⇧*[f2] Tf ≘ T → ∀g2,Tg. ⇧*[g2] Tg ≘ T →
                    ∀f1,g1. H_pr_pat_div f2 g2 f1 g1 →
                    ∃∃T0. ⇧*[f1] T0 ≘ Tf & ⇧*[g1] T0 ≘ Tg.
#f2 #Tf #T #H elim H -f2 -Tf -T
[ #f2 #s #g2 #Tg #H #f1 #g1 #_
  lapply (lifts_inv_sort2 … H) -H #H destruct
  /2 width=3 by ex2_intro/
| #f2 #jf #j #Hf2 #g2 #Tg #H #f1 #g1 #H0
  elim (lifts_inv_lref2 … H) -H #jg #Hg2 #H destruct
  elim (H0 … Hf2 Hg2) -H0 -j /3 width=3 by lifts_lref, ex2_intro/
| #f2 #l #g2 #Tg #H #f1 #g1 #_
  lapply (lifts_inv_gref2 … H) -H #H destruct
  /2 width=3 by ex2_intro/
| #f2 #p #I #Vf #V #Tf #T #_ #_ #IHV #IHT #g2 #X #H #f1 #g1 #H0
  elim (lifts_inv_bind2 … H) -H #Vg #Tg #HVg #HTg #H destruct
  elim (IHV … HVg … H0) -IHV -HVg
  elim (IHT … HTg) -IHT -HTg [ |*: /2 width=8 by pr_pat_div_push_bi/ ]
  /3 width=5 by lifts_bind, ex2_intro/
| #f2 #I #Vf #V #Tf #T #_ #_ #IHV #IHT #g2 #X #H #f1 #g1 #H0
  elim (lifts_inv_flat2 … H) -H #Vg #Tg #HVg #HTg #H destruct
  elim (IHV … HVg … H0) -IHV -HVg
  elim (IHT … HTg … H0) -IHT -HTg -H0
  /3 width=5 by lifts_flat, ex2_intro/
]
qed-.

lemma lifts_div4_one: ∀f,Tf,T. ⇧*[⫯f] Tf ≘ T →
                      ∀T1. ⇧[1] T1 ≘ T →
                      ∃∃T0. ⇧[1] T0 ≘ Tf & ⇧*[f] T0 ≘ T1.
/4 width=6 by lifts_div4, pr_pat_div_id_dx, pr_pat_div_push_next/ qed-.

theorem lifts_div3: ∀f2,T,T2. ⇧*[f2] T2 ≘ T → ∀f,T1. ⇧*[f] T1 ≘ T →
                    ∀f1. f2 ⊚ f1 ≘ f → ⇧*[f1] T1 ≘ T2.
#f2 #T #T2 #H elim H -f2 -T -T2
[ #f2 #s #f #T1 #H >(lifts_inv_sort2 … H) -T1 //
| #f2 #i2 #i #Hi2 #f #T1 #H #f1 #Ht21 elim (lifts_inv_lref2 … H) -H
  #i1 #Hi1 #H destruct /3 width=6 by lifts_lref, pr_after_des_pat_dx/
| #f2 #l #f #T1 #H >(lifts_inv_gref2 … H) -T1 //
| #f2 #p #I #W2 #W #U2 #U #_ #_ #IHW #IHU #f #T1 #H
  elim (lifts_inv_bind2 … H) -H #W1 #U1 #HW1 #HU1 #H destruct
  /4 width=3 by lifts_bind, after_O2/
| #f2 #I #W2 #W #U2 #U #_ #_ #IHW #IHU #f #T1 #H
  elim (lifts_inv_flat2 … H) -H #W1 #U1 #HW1 #HU1 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.

(* Basic_1: was: lift1_lift1 (left to right) *)
(* Basic_1: includes: lift_free (left to right) lift_d lift1_xhg (right to left) lift1_free (right to left) *)
(* Basic_2A1: includes: lift_trans_be lift_trans_le lift_trans_ge lifts_lift_trans_le lifts_lift_trans *)
theorem lifts_trans: ∀f1,T1,T. ⇧*[f1] T1 ≘ T → ∀f2,T2. ⇧*[f2] T ≘ T2 →
                     ∀f. f2 ⊚ f1 ≘ f → ⇧*[f] T1 ≘ T2.
#f1 #T1 #T #H elim H -f1 -T1 -T
[ #f1 #s #f2 #T2 #H >(lifts_inv_sort1 … H) -T2 //
| #f1 #i1 #i #Hi1 #f2 #T2 #H #f #Ht21 elim (lifts_inv_lref1 … H) -H
  #i2 #Hi2 #H destruct /3 width=6 by lifts_lref, pr_after_des_pat/
| #f1 #l #f2 #T2 #H >(lifts_inv_gref1 … H) -T2 //
| #f1 #p #I #W1 #W #U1 #U #_ #_ #IHW #IHU #f2 #T2 #H
  elim (lifts_inv_bind1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /4 width=3 by lifts_bind, after_O2/
| #f1 #I #W1 #W #U1 #U #_ #_ #IHW #IHU #f2 #T2 #H
  elim (lifts_inv_flat1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.

lemma lifts_trans4_one (f) (T1) (T2):
                       ∀T. ⇧[1]T1 ≘ T → ⇧*[⫯f]T ≘ T2 →
                       ∃∃T0. ⇧*[f]T1 ≘ T0 & ⇧[1]T0 ≘ T2.
/4 width=6 by lifts_trans, lifts_split_trans, pr_after_push_unit/ qed-.

(* Basic_2A1: includes: lift_conf_O1 lift_conf_be *)
theorem lifts_conf: ∀f1,T,T1. ⇧*[f1] T ≘ T1 → ∀f,T2. ⇧*[f] T ≘ T2 →
                    ∀f2. f2 ⊚ f1 ≘ f → ⇧*[f2] T1 ≘ T2.
#f1 #T #T1 #H elim H -f1 -T -T1
[ #f1 #s #f #T2 #H >(lifts_inv_sort1 … H) -T2 //
| #f1 #i #i1 #Hi1 #f #T2 #H #f2 #Ht21 elim (lifts_inv_lref1 … H) -H
  #i2 #Hi2 #H destruct /3 width=6 by lifts_lref, pr_after_des_pat_sn/
| #f1 #l #f #T2 #H >(lifts_inv_gref1 … H) -T2 //
| #f1 #p #I #W #W1 #U #U1 #_ #_ #IHW #IHU #f #T2 #H
  elim (lifts_inv_bind1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /4 width=3 by lifts_bind, after_O2/
| #f1 #I #W #W1 #U #U1 #_ #_ #IHW #IHU #f #T2 #H
  elim (lifts_inv_flat1 … H) -H #W2 #U2 #HW2 #HU2 #H destruct
  /3 width=3 by lifts_flat/
]
qed-.

(* Advanced proprerties *****************************************************)

(* Basic_2A1: includes: lift_inj *)
lemma lifts_inj: ∀f. is_inj2 … (lifts f).
#f #T1 #U #H1 #T2 #H2 lapply (pr_after_isi_dx 𝐢  … f)
/3 width=6 by lifts_div3, lifts_fwd_isid/
qed-.

(* Basic_2A1: includes: lift_mono *)
lemma lifts_mono: ∀f,T. is_mono … (lifts f T).
#f #T #U1 #H1 #U2 #H2 lapply (pr_after_isi_sn 𝐢  … f)
/3 width=6 by lifts_conf, lifts_fwd_isid/
qed-.

lemma liftable2_sn_bi: ∀R. liftable2_sn R → liftable2_bi R.
#R #HR #T1 #T2 #HT12 #f #U1 #HTU1 #U2 #HTU2
elim (HR … HT12 … HTU1) -HR -T1 #X #HTX #HUX
<(lifts_mono … HTX … HTU2) -T2 -U2 -f //
qed-.

lemma deliftable2_sn_bi: ∀R. deliftable2_sn R → deliftable2_bi R.
#R #HR #U1 #U2 #HU12 #f #T1 #HTU1 #T2 #HTU2
elim (HR … HU12 … HTU1) -HR -U1 #X #HUX #HTX
<(lifts_inj … HUX … HTU2) -U2 -T2 -f //
qed-.

lemma lifts_trans_uni (T):
      ∀l1,T1. ⇧[l1] T1 ≘ T →
      ∀l2,T2. ⇧[l2] T ≘ T2 → ⇧[l1+l2] T1 ≘ T2.
#T #l1 #T1 #HT1 #l2 #T2 #HT2
@(lifts_trans … HT1 … HT2) //
qed-.
