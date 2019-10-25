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

include "ground_2/xoa/ex_7_8.ma".
include "basic_2/rt_computation/cpms_drops.ma".
include "basic_2/rt_conversion/cpce.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* Advanced properties ******************************************************)

lemma cpce_ldef_drops (h) (G) (K) (V):
      ∀i,L. ⇩*[i] L ≘ K.ⓓV → ⦃G,L⦄ ⊢ #i ⬌η[h] #i.
#h #G #K #V #i elim i -i
[ #L #HLK
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  /2 width=1 by cpce_ldef/
| #i #IH #L #HLK
  elim (drops_inv_succ … HLK) -HLK #Z #Y #HYK #H destruct
  /3 width=3 by cpce_lref/
]
qed.

lemma cpce_ldec_drops (h) (G) (K) (W):
      (∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
      ∀i,L. ⇩*[i] L ≘ K.ⓛW → ⦃G,L⦄ ⊢ #i ⬌η[h] #i.
#h #G #K #W #HW #i elim i -i
[ #L #HLK
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  /3 width=5 by cpce_ldec/
| #i #IH #L #HLK
  elim (drops_inv_succ … HLK) -HLK #Z #Y #HYK #H destruct
  /3 width=3 by cpce_lref/
]
qed.

lemma cpce_eta_drops (h) (G) (K) (W):
      ∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U →
      ∀W1. ⦃G,K⦄ ⊢ W ⬌η[h] W1 → ∀V1. ⦃G,K⦄ ⊢ V ⬌η[h] V1 →
      ∀i,L. ⇩*[i] L ≘ K.ⓛW → ∀W2. ⇧*[↑i] W1 ≘ W2 →
      ∀V2. ⇧*[↑i] V1 ≘ V2 → ⦃G,L⦄ ⊢ #i ⬌η[h] ⓝW2.+ⓛV2.ⓐ#0.#↑i.
#h #G #K #W #n #p #V #U #HWU #W1 #HW1 #V1 #HV1 #i elim i -i
[ #L #HLK #W2 #HW12 #V2 #HV12
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  /2 width=8 by cpce_eta/
| #i #IH #L #HLK #W2 #HW12 #V2 #HV12
  elim (drops_inv_succ … HLK) -HLK #I #Y #HYK #H destruct
  elim (lifts_split_trans … HW12 (𝐔❴↑i❵) (𝐔❴1❵)) [| // ] #XW #HXW1 #HXW2
  elim (lifts_split_trans … HV12 (𝐔❴↑i❵) (𝐔❴1❵)) [| // ] #XV #HXV1 #HXV2
  /6 width=9 by cpce_lref, lifts_push_lref, lifts_bind, lifts_flat/
]
qed.

lemma cpce_lref_drops (h) (G) (K) (i):
      ∀T. ⦃G,K⦄ ⊢ #i ⬌η[h] T → ∀j,L. ⇩*[j] L ≘ K →
      ∀U. ⇧*[j] T ≘ U → ⦃G,L⦄ ⊢ #(j+i) ⬌η[h] U.
#h #G #K #i #T #Hi #j elim j -j
[ #L #HLK #U #HTU
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  lapply (lifts_fwd_isid … HTU ?) -HTU [ // ] #H destruct //
| #j #IH #Y #HYK #X #HTX -Hi
  elim (drops_inv_succ … HYK) -HYK #I #L #HLK #H destruct
  elim (lifts_split_trans … HTX (𝐔❴j❵) (𝐔❴1❵)) [| // ] #U #HTU #HUX
  /3 width=3 by cpce_lref/
]
qed-.

(* Advanced inversion lemmas ************************************************)

axiom cpce_inv_lref_sn_drops_pair (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀I,K,W. ⇩*[i] L ≘ K.ⓑ{I}W →
      ∨∨ ∧∧ Abbr = I & #i = X2
       | ∧∧ Abst = I & ∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥ & #i = X2
       | ∃∃n,p,W1,W2,V,V1,V2,U. Abst = I & ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U
                              & ⦃G,K⦄ ⊢ W ⬌η[h] W1 & ⇧*[↑i] W1 ≘ W2
                              & ⦃G,K⦄ ⊢ V ⬌η[h] V1 & ⇧*[↑i] V1 ≘ V2
                              & ⓝW2.+ⓛV2.ⓐ#0.#(↑i) = X2.

axiom cpce_inv_lref_sn_drops_ldef (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀K,V. ⇩*[i] L ≘ K.ⓓV → #i = X2.

axiom cpce_inv_lref_sn_drops_ldec (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀K,W. ⇩*[i] L ≘ K.ⓛW →
      ∨∨ ∧∧ ∀n,p,V,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥ & #i = X2
       | ∃∃n,p,W1,W2,V,V1,V2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U
                              & ⦃G,K⦄ ⊢ W ⬌η[h] W1 & ⇧*[↑i] W1 ≘ W2
                              & ⦃G,K⦄ ⊢ V ⬌η[h] V1 & ⇧*[↑i] V1 ≘ V2
                              & ⓝW2.+ⓛV2.ⓐ#0.#(↑i) = X2.
(*
#h #G #i elim i -i
[ #L #X2 #HX2 #I #K #HLK
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  /2 width=1 by cpce_inv_zero_sn/
| #i #IH #L0 #X0 #HX0 #J #K #H0
  elim (drops_inv_succ … H0) -H0 #I #L #HLK #H destruct
  elim (cpce_inv_lref_sn … HX0) -HX0 #X2 #HX2 #HX20
  elim (IH … HX2 … HLK) -IH -I -L *
  [ #HJ #H destruct
    lapply (lifts_inv_lref1_uni … HX20) -HX20 #H destruct
    /4 width=7 by or_introl, conj/
  | #n #p #W #V1 #V2 #W2 #U #HWU #HV12 #HVW2 #H1 #H2 destruct
    elim (lifts_inv_bind1 … HX20) -HX20 #X2 #X #HWX2 #HX #H destruct
    elim (lifts_inv_flat1 … HX) -HX #X0 #X1 #H0 #H1 #H destruct
    lapply (lifts_inv_push_zero_sn … H0) -H0 #H destruct
    elim (lifts_inv_push_succ_sn … H1) -H1 #j #Hj #H destruct
    lapply (lifts_inv_lref1_uni … Hj) -Hj #H destruct
    /4 width=12 by lifts_trans_uni, ex5_7_intro, or_intror/
  ]
]
qed-.

lemma cpce_inv_zero_sn_drops (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀I,K. ⇩*[i] L ≘ K.ⓘ{I} →
      (∀n,p,W,V,U. I = BPair Abst W → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
      #i = X2.
#h #G #i #L #X2 #HX2 #I #K #HLK #HI
elim (cpce_inv_lref_sn_drops_bind … HX2 … HLK) -L *
[ #_ #H //
| #n #p #W #V1 #V2 #W2 #U #HWU #_ #_ #H destruct
  elim (HI … HWU) -n -p -K -X2 -V1 -V2 -W2 -U -i //
]
qed-.
*)
(* Properties with uniform slicing for local environments *******************)

axiom cpce_lifts_sn (h) (G):
      d_liftable2_sn … lifts (cpce h G).
(*
#h #G #K #T1 #T2 #H elim H -G -K -T1 -T2
[ #G #K #s #b #f #L #HLK #X #HX
  lapply (lifts_inv_sort1 … HX) -HX #H destruct
  /2 width=3 by cpce_sort, lifts_sort, ex2_intro/
| #G #i #b #f #L #HLK #X #HX
  elim (lifts_inv_lref1 … HX) -HX #j #Hf #H destruct
  @(ex2_intro … (#j))
  [ /2 width=1 by lifts_lref/
  | @cpce_zero_drops #n #p #Y #W #V #U #HY #_
    elim (drops_inv_atom2 … HLK) -HLK #j1 #g #HLK #Hg
    elim (after_at_fwd … Hf … Hg) -f #j2 #_ #Hj -g -i
    lapply (at_inv_uni … Hj) -Hj #H destruct
    lapply (drops_conf … HLK … HY ??) -L [3:|*: // ] #H
    elim (drops_inv_atom1 … H) -H #H #_ destruct
  ]
| #G #K #I #HI #b #f #L #HLK #X #HX
  elim (lifts_inv_lref1 … HX) -HX #j #Hf #H destruct
  @(ex2_intro … (#j))
  [ /2 width=1 by lifts_lref/
  | elim (drops_split_trans_bind2 … HLK … Hf) -HLK -Hf #J #Y1 #HY1 #HK #HIJ
    @cpce_zero_drops #n #p #Y2 #W #V #U #HY2 #HWU
    lapply (drops_mono … HY2 … HY1) -L #H destruct
    elim (liftsb_inv_pair_dx … HIJ) -HIJ #X #HXW #H destruct
    elim (cpms_inv_lifts_sn … HWU … HK … HXW) -b -Y1 -W #X0 #H #HXU
    elim (lifts_inv_bind2 … H) -H #V0 #U0 #_ #_ #H destruct -f -j -V -U
    /2 width=7 by/
  ]
| #n #p #G #K #W #V1 #V2 #W2 #U #HWU #_ #HVW2 #IH #b #f #L #HLK #X #HX
  elim (lifts_inv_lref1 … HX) -HX #j #Hf #H destruct
  elim (drops_split_trans_bind2 … HLK … Hf) -HLK #J #Y #HY #HK #HIJ
  elim (liftsb_inv_pair_sn … HIJ) -HIJ #W0 #HW0 #H destruct
  elim (cpms_lifts_sn … HWU … HK … HW0) -HWU -HW0 #X #H #HWU0
  elim (lifts_inv_bind1 … H) -H #V0 #U0 #HV10 #HU0 #H destruct
  elim (IH … HK … HV10) -IH -HK -HV10 #VX #HV2X #HV0X
  elim (lifts_total W2 f) #WX2 #HWX2
  lapply (lifts_trans … HVW2 … HWX2 ??) [3:|*: // ] -HVW2 #HVX2
  @(ex2_intro … (+ⓛWX2.ⓐ#O.#(↑j)))
  [ /5 width=1 by lifts_lref, lifts_bind, lifts_flat, at_S1/
  | /4 width=18 by cpce_eta_drops, lifts_conf, after_uni_succ_dx/
  ]
| #I #G #K #T #U #i #_ #HTU #IH #b #f #L #HLK #X #HX
  elim (lifts_inv_lref1 … HX) -HX #x #Hf #H destruct
  elim (at_inv_nxx … Hf) -Hf [|*: // ] #j #Hf #H destruct
  elim (drops_split_trans_bind2 … HLK) -HLK [|*: // ] #Z #Y #HLY #HYK #_ -I
  lapply (drops_isuni_fwd_drop2 … HLY) -HLY [ // ] #HLY  
  elim (IH … HYK) -IH -HYK [|*: /2 width=2 by lifts_lref/ ] -i #T0 #HT0 #Hj
  elim (lifts_total U f) #U0 #HU0
  lapply (lifts_trans … HTU … HU0 ??) [3:|*: // ] -HTU #HTU0
  lapply (lifts_conf … HT0 … HTU0 ??) -T
  [3:|*: /2 width=3 by after_uni_succ_dx/ ] #HTU0 >plus_S1
  /3 width=7 by cpce_lref_drops, ex2_intro/
| #G #K #l #b #f #L #HLK #X #HX
  lapply (lifts_inv_gref1 … HX) -HX #H destruct
  /2 width=3 by cpce_gref, lifts_gref, ex2_intro/
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #b #f #L #HLK #X #HX
  elim (lifts_inv_bind1 … HX) -HX #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HLK … HVW1) -IHV #W2 #HVW2 #HW12
  elim (IHT … HTU1) -IHT -HTU1 [|*: /3 width=3 by drops_skip, ext2_pair/ ] -HVW1 #U2 #HTU2 #HU12
  /3 width=5 by cpce_bind, lifts_bind, ex2_intro/
| #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #b #f #L #HLK #X #HX
  elim (lifts_inv_flat1 … HX) -HX #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HLK … HVW1) -IHV -HVW1 #W2 #HVW2 #HW12
  elim (IHT … HLK … HTU1) -IHT -HTU1 -HLK #U2 #HTU2 #HU12
  /3 width=5 by cpce_flat, lifts_flat, ex2_intro/
]
qed-.
*)
lemma cpce_lifts_bi (h) (G):
      d_liftable2_bi … lifts (cpce h G).
/3 width=12 by cpce_lifts_sn, d_liftable2_sn_bi, lifts_mono/ qed-.

(* Inversion lemmas with uniform slicing for local environments *************)

axiom cpce_inv_lifts_sn (h) (G):
      d_deliftable2_sn … lifts (cpce h G).
(*
#h #G #K #T1 #T2 #H elim H -G -K -T1 -T2
[ #G #K #s #b #f #L #HLK #X #HX
  lapply (lifts_inv_sort2 … HX) -HX #H destruct
  /2 width=3 by cpce_sort, lifts_sort, ex2_intro/
| #G #i #b #f #L #HLK #X #HX
  elim (lifts_inv_lref2 … HX) -HX #j #Hf #H destruct
  @(ex2_intro … (#j))
  [ /2 width=1 by lifts_lref/
  | @cpce_zero_drops #n #p #Y #W #V #U #HY #_ -n -p -G -V -U -i
    elim (drops_inv_atom1 … HLK) -HLK #H #_ destruct -b -f
    elim (drops_inv_atom1 … HY) -HY #H #_ destruct
  ]
| #G #K #I #HI #b #f #L #HLK #X #HX
  elim (lifts_inv_lref2 … HX) -HX #j #Hf #H destruct
  @(ex2_intro … (#j))
  [ /2 width=1 by lifts_lref/
  | elim (at_inv_xxp … Hf) -Hf [| // ] #g #H1 #H2 destruct
    elim (drops_inv_skip1 … HLK) -HLK #J #Y #HKY #HIJ #H destruct
    @cpce_zero #n #p #W #V #U #H #HWU destruct
    elim (liftsb_inv_pair_sn … HIJ) -HIJ #X #HXW #H destruct
    elim (cpms_lifts_sn … HWU … HKY … HXW) -b -Y -W #X0 #H #HXU
    elim (lifts_inv_bind1 … H) -H #V0 #U0 #_ #_ #H destruct -V -U
    /2 width=7 by/
  ]
| #n #p #G #K #W #V1 #V2 #W2 #U #HWU #_ #HVW2 #IH #b #f #L #HLK #X #HX
  elim (lifts_inv_lref2 … HX) -HX #j #Hf #H destruct
  elim (at_inv_xxp … Hf) -Hf [| // ] #g #H1 #H2 destruct
  elim (drops_inv_skip1 … HLK) -HLK #J #Y #HKY #HIJ #H destruct
  elim (liftsb_inv_pair_dx … HIJ) -HIJ #W0 #HW0 #H destruct
  elim (cpms_inv_lifts_sn … HWU … HKY … HW0) -HWU -HW0 #X #H #HWU0
  elim (lifts_inv_bind2 … H) -H #V0 #U0 #HV10 #HU0 #H destruct
  elim (IH … HKY … HV10) -IH -HKY -HV10 #VX #HV2X #HV0X
  lapply (lifts_trans … HV2X … HVW2 (↑g) ?)
  [ /3 width=5 by after_isid_sn, after_next/ ] -V2 #H
  elim (lifts_split_trans … H 𝐔❴1❵ (⫯g) ?)
  [| /3 width=7 by after_isid_dx, after_push/ ] #VX2 #HVX2 #HVW2
  /5 width=10 by cpce_eta, lifts_flat, lifts_bind, lifts_lref, ex2_intro/
| #I #G #K #T #U #i #_ #HTU #IH #b #f #L #HLK #X #HX
  elim (lifts_inv_lref2 … HX) -HX #x #Hf #H destruct
(**) (* this part should be a lemma *)
  elim (at_inv_xxn … Hf) -Hf [2,4: // ] *
  [ #g #j #Hij #H1 #H2 destruct
    elim (drops_inv_skip1 … HLK) -HLK #J #Y #HLK #_ #H destruct -I
  | #g #Hij #H destruct
    lapply (drops_inv_drop1 … HLK) -HLK #HLK
  ]
(**)
  elim (IH … HLK) -IH -HLK [1,4:|*: /2 width=2 by lifts_lref/ ] -i #T0 #HT0 #Hj
  lapply (lifts_trans … HT0 … HTU (↑g) ?)
  [1,3: /3 width=5 by after_isid_sn, after_next/ ] -T #H
  elim (lifts_split_trans … H 𝐔❴1❵ (⫯g) ?)
  [2,4: /3 width=7 by after_isid_dx, after_push/ ] #U0 #HTU0 #HU0
  /3 width=5 by cpce_lref, ex2_intro/
| #G #K #l #b #f #L #HLK #X #HX
  lapply (lifts_inv_gref2 … HX) -HX #H destruct
  /2 width=3 by cpce_gref, lifts_gref, ex2_intro/
| #p #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #b #f #L #HLK #X #HX
  elim (lifts_inv_bind2 … HX) -HX #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HLK … HVW1) -IHV #W2 #HVW2 #HW12
  elim (IHT … HTU1) -IHT -HTU1 [|*: /3 width=3 by drops_skip, ext2_pair/ ] -HVW1 #U2 #HTU2 #HU12
  /3 width=5 by cpce_bind, lifts_bind, ex2_intro/
| #I #G #K #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #b #f #L #HLK #X #HX
  elim (lifts_inv_flat2 … HX) -HX #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HLK … HVW1) -IHV -HVW1 #W2 #HVW2 #HW12
  elim (IHT … HLK … HTU1) -IHT -HTU1 -HLK #U2 #HTU2 #HU12
  /3 width=5 by cpce_flat, lifts_flat, ex2_intro/
]
qed-.
*)
lemma cpce_inv_lifts_bi (h) (G):
      d_deliftable2_bi … lifts (cpce h G).
/3 width=12 by cpce_inv_lifts_sn, d_deliftable2_sn_bi, lifts_inj/ qed-.
