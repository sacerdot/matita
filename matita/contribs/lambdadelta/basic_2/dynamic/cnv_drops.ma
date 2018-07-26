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

include "basic_2/rt_computation/cpms_drops.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT_SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Advanced dproperties *****************************************************)

(* Basic_2A1: uses: snv_lref *)
lemma cnv_lref_drops (a) (h) (G): ∀I,K,V,i,L. ⦃G, K⦄ ⊢ V ![a, h] →
                                  ⬇*[i] L ≘ K.ⓑ{I}V →  ⦃G, L⦄ ⊢ #i ![a, h].
#a #h #G #I #K #V #i elim i -i
[ #L #HV #H
  lapply (drops_fwd_isid … H ?) -H // #H destruct
  /2 width=1 by cnv_zero/
| #i #IH #L #HV #H
  elim (drops_inv_succ … H) -H #J0 #K0 #HK0 #H destruct
  /3 width=1 by cnv_lref/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: snv_inv_lref *)
lemma cnv_inv_lref_drops (a) (h) (G):
                         ∀i,L. ⦃G, L⦄ ⊢ #i ![a, h] →
                         ∃∃I,K,V. ⬇*[i] L ≘ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ![a, h].
#a #h #G #i elim i -i
[ #L #H
  elim (cnv_inv_zero … H) -H #I #K #V #HV #H destruct
  /3 width=5 by drops_refl, ex2_3_intro/
| #i #IH #X #H
  elim (cnv_inv_lref … H) -H #I #L #HL #H destruct
  elim (IH … HL) -IH -HL #J #K #V #HLK #HV
  /3 width=5 by drops_drop, ex2_3_intro/
]
qed-.

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: uses: snv_lift *)
lemma cnv_lifts (a) (h): ∀G. d_liftable1 (cnv a h G).
#a #h #G #K #T
@(fqup_wf_ind_eq (Ⓣ) … G K T) -G -K -T #G0 #K0 #T0 #IH #G #K * * [|||| * ]
[ #s #HG #HK #HT #_ #b #f #L #_ #X #H2 destruct
  >(lifts_inv_sort1 … H2) -X -K -f //
| #i #HG #HK #HT #H1 #b #f #L #HLK #X #H2 destruct
  elim (cnv_inv_lref_drops … H1) -H1 #I0 #K0 #V #HK0 #HV
  elim (lifts_inv_lref1 … H2) -H2 #j #Hf #H destruct
(**) (* this should be a lemma *)
  lapply (drops_trans … HLK … HK0 ??) -HLK [3,6: |*: // ] #H
  elim (drops_split_trans … H) -H [1,6: |*: /2 width=6 by after_uni_dx/ ] #Y #HL #HY
  lapply (drops_tls_at … Hf … HY) -HY #HY
  elim (drops_inv_skip2 … HY) -HY #Z #L0 #HLK0 #HZ #H destruct
  elim (liftsb_inv_pair_sn … HZ) -HZ #W #HVW #H destruct
(**) (* end of the lemma *)
  /4 width=8 by cnv_lref_drops, fqup_lref, drops_inv_gen/
| #l #HG #HK #HT #H1 #b #f #L #_ #X #_ destruct
  elim (cnv_inv_gref … H1)
| #p #I #V #T #HG #HK #HT #H1 #b #f #L #HLK #X #H2 destruct
  elim (cnv_inv_bind … H1) -H1 #HV #HT
  elim (lifts_inv_bind1 … H2) -H2 #W #U #HVW #HTU #H destruct
  /5 width=8 by cnv_bind, drops_skip, ext2_pair/
| #V #T #HG #HK #HT #H1 #b #f #L #HLK #X #H2 destruct
  elim (cnv_inv_appl … H1) #n #p #W0 #U0 #Ha #HV #HT #HVW0 #HTW0
  elim (lifts_inv_flat1 … H2) -H2 #W #U #HVW #HTU #H destruct
  elim (lifts_total W0 f)
  elim (lifts_total U0 (⫯f))
  /4 width=17 by cnv_appl, cpms_lifts_bi, lifts_bind/
| #V #T #HG #HK #HT #H1 #b #f #L #HLK #X #H2 destruct
  elim (cnv_inv_cast … H1) #U0 #HV #HT #HVU0 #HTU0
  elim (lifts_inv_flat1 … H2) -H2 #W #U #HVW #HTU #H destruct
  elim (lifts_total U0 f)
  /3 width=12 by cnv_cast, cpms_lifts_bi/
]
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: uses: snv_inv_lift *)
lemma cnv_inv_lifts (a) (h): ∀G. d_deliftable1 (cnv a h G).
#a #h #G #L #U
@(fqup_wf_ind_eq (Ⓣ) … G L U) -G -L -U #G0 #L0 #U0 #IH #G #L * * [|||| * ]
[ #s #HG #HL #HU #H1 #b #f #K #HLK #X #H2 destruct
  >(lifts_inv_sort2 … H2) -X -L -f //
| #j #HG #HL #HU #H1 #b #f #K #HLK #X #H2 destruct
  elim (cnv_inv_lref_drops … H1) -H1 #I0 #L0 #W #HL0 #HW
  elim (lifts_inv_lref2 … H2) -H2 #i #Hf #H destruct
(**) (* this should be a lemma *)
  lapply (drops_split_div … HLK (𝐔❴i❵) ???) -HLK [4,8: * |*: // ] #Y0 #HK #HLY0
  lapply (drops_conf … HL0 … HLY0 ??) -HLY0 [3,6: |*: /2 width=6 by after_uni_dx/ ] #HLY0
  lapply (drops_tls_at … Hf … HLY0) -HLY0 #HLY0
  elim (drops_inv_skip1 … HLY0) -HLY0 #Z #K0 #HLK0 #HZ #H destruct
  elim (liftsb_inv_pair_dx … HZ) -HZ #V #HVW #H destruct
(**) (* end of the lemma *)
  /4 width=8 by cnv_lref_drops, fqup_lref, drops_inv_F/
| #l #HG #HL #HU #H1 #b #f #K #_ #X #_ destruct
  elim (cnv_inv_gref … H1)
| #p #I #W #U #HG #HL #HU #H1 #b #f #K #HLK #X #H2 destruct
  elim (cnv_inv_bind … H1) -H1 #HW #HU
  elim (lifts_inv_bind2 … H2) -H2 #V #T #HVW #HTU #H destruct
  /5 width=8 by cnv_bind, drops_skip, ext2_pair/
| #W #U #HG #HL #HU #H1 #b #f #K #HLK #X #H2 destruct
  elim (cnv_inv_appl … H1) #n #p #W0 #U0 #Ha #HW #HU #HW0 #HU0
  elim (lifts_inv_flat2 … H2) -H2 #V #T #HVW #HTU #H destruct
  elim (cpms_inv_lifts_sn … HW0 … HLK … HVW) -HW0 #V0 #HVW0 #HV0
  elim (cpms_inv_lifts_sn … HU0 … HLK … HTU) -HU0 #X0 #H #HT0
  elim (lifts_inv_bind2 … H) -H #X #T0 #HX #HTU0 #H destruct
  lapply (lifts_inj … HX … HVW0) -HX #H destruct
  /3 width=8 by cnv_appl/
| #W #U #HG #HL #HU #H1 #b #f #K #HLK #X #H2 destruct
  elim (cnv_inv_cast … H1) #U0 #HW #HU #HWU0 #HU0
  elim (lifts_inv_flat2 … H2) -H2 #V #T #HVW #HTU #H destruct
  elim (cpms_inv_lifts_sn … HWU0 … HLK … HVW) -HWU0 #V0 #HVU0 #HV0
  elim (cpms_inv_lifts_sn … HU0 … HLK … HTU) -HU0 #X #HX #HTV0
  lapply (lifts_inj … HX … HVU0) -HX #H destruct
  /3 width=8 by cnv_cast/
]
qed-.
