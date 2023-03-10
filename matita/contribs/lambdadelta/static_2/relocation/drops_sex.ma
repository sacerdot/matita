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

include "static_2/relocation/lifts_lifts_bind.ma".
include "static_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with entrywise extension of context-sensitive relations *******)

(**) (* changed after commit 13218 *)
lemma sex_co_dropable_sn (RN) (RP):
      co_dropable_sn (sex RN RP).
#RN #RP #b #f #L1 #K1 #H elim H -f -L1 -K1
[ #f #Hf #_ #f2 #X #H #f1 #Hf2 >(sex_inv_atom1 … H) -X
  /4 width=3 by sex_atom, drops_atom, ex2_intro/
| #f #I1 #L1 #K1 #_ #IH #Hf #f2 #X #H #f1 #Hf2
  elim (pr_coafter_inv_next_sn … Hf2) -Hf2 [2,3: // ] #g2 #Hg2 #H2 destruct
  elim (sex_inv_push1 … H) -H #I2 #L2 #HL12 #HI12 #H destruct
  elim (IH … HL12 … Hg2) -g2
  /3 width=3 by pr_isu_inv_next, drops_drop, ex2_intro/
| #f #I1 #J1 #L1 #K1 #HLK #HJI1 #IH #Hf #f2 #X #H #f1 #Hf2
  lapply (pr_isu_inv_push … Hf ??) -Hf [3: |*: // ] #Hf
  lapply (drops_fwd_isid … HLK … Hf) -HLK #H0 destruct
  lapply (liftsb_fwd_isid … HJI1 … Hf) -HJI1 #H0 destruct
  elim (pr_coafter_inv_push_sn … Hf2) -Hf2 [1,3:* |*: // ] #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (sex_inv_push1 … H) | elim (sex_inv_next1 … H) ] -H #I2 #L2 #HL12 #HI12 #H destruct
  elim (IH … HL12 … Hg2) -g2 -IH /2 width=1 by pr_isu_isi/ #K2 #HK12 #HLK2
  lapply (drops_fwd_isid … HLK2 … Hf) -HLK2 #H0 destruct
  /4 width=3 by drops_refl, sex_next, sex_push, pr_isi_push, ex2_intro/
]
qed-.

lemma sex_liftable_co_dedropable_bi (RN) (RP):
      d_liftable2_sn … liftsb RN → d_liftable2_sn … liftsb RP →
      ∀f2,L1,L2. L1 ⪤[cfull,RP,f2] L2 → ∀f1,K1,K2. K1 ⪤[RN,RP,f1] K2 →
      ∀b,f. ⇩*[b,f] L1 ≘ K1 → ⇩*[b,f] L2 ≘ K2 →
      f ~⊚ f1 ≘ f2 → L1 ⪤[RN,RP,f2] L2.
#RN #RP #HRN #HRP #f2 #L1 #L2 #H elim H -f2 -L1 -L2 //
#g2 #I1 #I2 #L1 #L2 #HL12 #HI12 #IH #f1 #Y1 #Y2 #HK12 #b #f #HY1 #HY2 #H
[ elim (pr_coafter_inv_next … H) [ |*: // ] -H #g #g1 #Hg2 #H1 #H2 destruct
  elim (drops_inv_skip1 … HY1) -HY1 #J1 #K1 #HLK1 #HJI1 #H destruct
  elim (drops_inv_skip1 … HY2) -HY2 #J2 #K2 #HLK2 #HJI2 #H destruct
  elim (sex_inv_next … HK12) -HK12 #HK12 #HJ12
  elim (HRN … HJ12 … HLK1 … HJI1) -HJ12 -HJI1 #Z #Hz
  >(liftsb_mono … Hz … HJI2) -Z /3 width=9 by sex_next/
| elim (pr_coafter_inv_push … H) [1,2: |*: // ] -H *
  [ #g #g1 #Hg2 #H1 #H2 destruct
    elim (drops_inv_skip1 … HY1) -HY1 #J1 #K1 #HLK1 #HJI1 #H destruct
    elim (drops_inv_skip1 … HY2) -HY2 #J2 #K2 #HLK2 #HJI2 #H destruct
    elim (sex_inv_push … HK12) -HK12 #HK12 #HJ12
    elim (HRP … HJ12 … HLK1 … HJI1) -HJ12 -HJI1 #Z #Hz
    >(liftsb_mono … Hz … HJI2) -Z /3 width=9 by sex_push/
  | #g #Hg2 #H destruct
    lapply (drops_inv_drop1 … HY1) -HY1 #HLK1
    lapply (drops_inv_drop1 … HY2) -HY2 #HLK2
    /3 width=9 by sex_push/
  ]
]
qed-.

lemma sex_liftable_co_dedropable_sn (RN) (RP):
      (∀L. reflexive … (RN L)) → (∀L. reflexive … (RP L)) →
      d_liftable2_sn … liftsb RN → d_liftable2_sn … liftsb RP →
      co_dedropable_sn (sex RN RP).
#RN #RP #H1RN #H1RP #H2RN #H2RP #b #f #L1 #K1 #H elim H -f -L1 -K1
[ #f #Hf #X #f1 #H #f2 #Hf2 >(sex_inv_atom1 … H) -X
  /4 width=4 by drops_atom, sex_atom, ex3_intro/
| #f #I1 #L1 #K1 #_ #IHLK1 #K2 #f1 #HK12 #f2 #Hf2
  elim (pr_coafter_inv_next_sn … Hf2) -Hf2 [2,3: // ] #g2 #Hg2 #H destruct
  elim (IHLK1 … HK12 … Hg2) -K1
  /3 width=6 by drops_drop, sex_next, sex_push, ex3_intro/
| #f #I1 #J1 #L1 #K1 #HLK1 #HJI1 #IHLK1 #X #f1 #H #f2 #Hf2
  elim (pr_coafter_inv_push_sn … Hf2) -Hf2 [1,3: * |*: // ] #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (sex_inv_push1 … H) | elim (sex_inv_next1 … H) ] -H #J2 #K2 #HK12 #HJ12 #H destruct
  [ elim (H2RP … HJ12 … HLK1 … HJI1) | elim (H2RN … HJ12 … HLK1 … HJI1) ] -J1
  elim (IHLK1 … HK12 … Hg2) -K1
  /3 width=6 by drops_skip, sex_next, sex_push, ex3_intro/
]
qed-.

fact sex_dropable_dx_aux (RN) (RP):
     ∀b,f,L2,K2. ⇩*[b,f] L2 ≘ K2 → 𝐔❨f❩ →
     ∀f2,L1. L1 ⪤[RN,RP,f2] L2 → ∀f1. f ~⊚ f1 ≘ f2 →
     ∃∃K1. ⇩*[b,f] L1 ≘ K1 & K1 ⪤[RN,RP,f1] K2.
#RN #RP #b #f #L2 #K2 #H elim H -f -L2 -K2
[ #f #Hf #_ #f2 #X #H #f1 #Hf2 lapply (sex_inv_atom2 … H) -H
  #H destruct /4 width=3 by sex_atom, drops_atom, ex2_intro/
| #f #I2 #L2 #K2 #_ #IH #Hf #f2 #X #HX #f1 #Hf2
  elim (pr_coafter_inv_next_sn … Hf2) -Hf2 [2,3: // ] #g2 #Hg2 #H destruct
  elim (sex_inv_push2 … HX) -HX #I1 #L1 #HL12 #HI12 #H destruct
  elim (IH … HL12 … Hg2) -L2 -I2 -g2
  /3 width=3 by drops_drop, pr_isu_inv_next, ex2_intro/
| #f #I2 #J2 #L2 #K2 #_ #HJI2 #IH #Hf #f2 #X #HX #f1 #Hf2
  elim (pr_coafter_inv_push_sn … Hf2) -Hf2 [1,3: * |*: // ] #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (sex_inv_push2 … HX) | elim (sex_inv_next2 … HX) ] -HX #I1 #L1 #HL12 #HI12 #H destruct
  elim (IH … HL12 … Hg2) -L2 -g2 /2 width=3 by pr_isu_fwd_push/ #K1 #HLK1 #HK12
  lapply (pr_isu_inv_push … Hf ??) -Hf [3,6: |*: // ] #Hf
  lapply (liftsb_fwd_isid … HJI2 … Hf) #H destruct -HJI2
  lapply (drops_fwd_isid … HLK1 … Hf) #H destruct -HLK1
  /4 width=5 by sex_next, sex_push, drops_refl, pr_isi_push, ex2_intro/
]
qed-.

lemma sex_co_dropable_dx (RN) (RP):
      co_dropable_dx (sex RN RP).
/2 width=5 by sex_dropable_dx_aux/ qed-.

lemma sex_drops_conf_next (RN) (RP):
      ∀f2,L1,L2. L1 ⪤[RN,RP,f2] L2 →
      ∀b,f,I1,K1. ⇩*[b,f] L1 ≘ K1.ⓘ[I1] → 𝐔❨f❩ →
      ∀f1. f ~⊚ ↑f1 ≘ f2 →
      ∃∃I2,K2. ⇩*[b,f] L2 ≘ K2.ⓘ[I2] & K1 ⪤[RN,RP,f1] K2 & RN K1 I1 I2.
#RN #RP #f2 #L1 #L2 #HL12 #b #f #I1 #K1 #HLK1 #Hf #f1 #Hf2
elim (sex_co_dropable_sn … HLK1 … Hf … HL12 … Hf2) -L1 -f2 -Hf
#X #HX #HLK2 elim (sex_inv_next1 … HX) -HX
#I2 #K2 #HK12 #HI12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma sex_drops_conf_push (RN) (RP):
      ∀f2,L1,L2. L1 ⪤[RN,RP,f2] L2 →
      ∀b,f,I1,K1. ⇩*[b,f] L1 ≘ K1.ⓘ[I1] → 𝐔❨f❩ →
      ∀f1. f ~⊚ ⫯f1 ≘ f2 →
      ∃∃I2,K2. ⇩*[b,f] L2 ≘ K2.ⓘ[I2] & K1 ⪤[RN,RP,f1] K2 & RP K1 I1 I2.
#RN #RP #f2 #L1 #L2 #HL12 #b #f #I1 #K1 #HLK1 #Hf #f1 #Hf2
elim (sex_co_dropable_sn … HLK1 … Hf … HL12 … Hf2) -L1 -f2 -Hf
#X #HX #HLK2 elim (sex_inv_push1 … HX) -HX
#I2 #K2 #HK12 #HI12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma sex_drops_trans_next (RN) (RP):
      ∀f2,L1,L2. L1 ⪤[RN,RP,f2] L2 →
      ∀b,f,I2,K2. ⇩*[b,f] L2 ≘ K2.ⓘ[I2] → 𝐔❨f❩ →
      ∀f1. f ~⊚ ↑f1 ≘ f2 →
      ∃∃I1,K1. ⇩*[b,f] L1 ≘ K1.ⓘ[I1] & K1 ⪤[RN,RP,f1] K2 & RN K1 I1 I2.
#RN #RP #f2 #L1 #L2 #HL12 #b #f #I2 #K2 #HLK2 #Hf #f1 #Hf2
elim (sex_co_dropable_dx … HL12 … HLK2 … Hf … Hf2) -L2 -f2 -Hf
#X #HLK1 #HX elim (sex_inv_next2 … HX) -HX
#I1 #K1 #HK12 #HI12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma sex_drops_trans_push (RN) (RP): ∀f2,L1,L2. L1 ⪤[RN,RP,f2] L2 →
      ∀b,f,I2,K2. ⇩*[b,f] L2 ≘ K2.ⓘ[I2] → 𝐔❨f❩ →
      ∀f1. f ~⊚ ⫯f1 ≘ f2 →
      ∃∃I1,K1. ⇩*[b,f] L1 ≘ K1.ⓘ[I1] & K1 ⪤[RN,RP,f1] K2 & RP K1 I1 I2.
#RN #RP #f2 #L1 #L2 #HL12 #b #f #I2 #K2 #HLK2 #Hf #f1 #Hf2
elim (sex_co_dropable_dx … HL12 … HLK2 … Hf … Hf2) -L2 -f2 -Hf
#X #HLK1 #HX elim (sex_inv_push2 … HX) -HX
#I1 #K1 #HK12 #HI12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma drops_sex_trans_next (RN) (RP):
      (∀L. reflexive ? (RN L)) → (∀L. reflexive ? (RP L)) →
      d_liftable2_sn … liftsb RN → d_liftable2_sn … liftsb RP →
      ∀f1,K1,K2. K1 ⪤[RN,RP,f1] K2 →
      ∀b,f,I1,L1. ⇩*[b,f] L1.ⓘ[I1] ≘ K1 →
      ∀f2. f ~⊚ f1 ≘ ↑f2 →
      ∃∃I2,L2. ⇩*[b,f] L2.ⓘ[I2] ≘ K2 & L1 ⪤[RN,RP,f2] L2 & RN L1 I1 I2 & L1.ⓘ[I1] ≡[f] L2.ⓘ[I2].
#RN #RP #H1RN #H1RP #H2RN #H2RP #f1 #K1 #K2 #HK12 #b #f #I1 #L1 #HLK1 #f2 #Hf2
elim (sex_liftable_co_dedropable_sn … H1RN H1RP H2RN H2RP … HLK1 … HK12 … Hf2) -K1 -f1 -H1RN -H1RP -H2RN -H2RP
#X #HX #HLK2 #H1L12 elim (sex_inv_next1 … HX) -HX
#I2 #L2 #H2L12 #HI12 #H destruct /2 width=6 by ex4_2_intro/
qed-.

lemma drops_sex_trans_push (RN) (RP):
      (∀L. reflexive ? (RN L)) → (∀L. reflexive ? (RP L)) →
      d_liftable2_sn … liftsb RN → d_liftable2_sn … liftsb RP →
      ∀f1,K1,K2. K1 ⪤[RN,RP,f1] K2 →
      ∀b,f,I1,L1. ⇩*[b,f] L1.ⓘ[I1] ≘ K1 →
      ∀f2. f ~⊚ f1 ≘ ⫯f2 →
      ∃∃I2,L2. ⇩*[b,f] L2.ⓘ[I2] ≘ K2 & L1 ⪤[RN,RP,f2] L2 & RP L1 I1 I2 & L1.ⓘ[I1] ≡[f] L2.ⓘ[I2].
#RN #RP #H1RN #H1RP #H2RN #H2RP #f1 #K1 #K2 #HK12 #b #f #I1 #L1 #HLK1 #f2 #Hf2
elim (sex_liftable_co_dedropable_sn … H1RN H1RP H2RN H2RP … HLK1 … HK12 … Hf2) -K1 -f1 -H1RN -H1RP -H2RN -H2RP
#X #HX #HLK2 #H1L12 elim (sex_inv_push1 … HX) -HX
#I2 #L2 #H2L12 #HI12 #H destruct /2 width=6 by ex4_2_intro/
qed-.

lemma drops_atom2_sex_conf (RN) (RP):
      ∀b,f1,L1. ⇩*[b,f1] L1 ≘ ⋆ → 𝐔❨f1❩ →
      ∀f,L2. L1 ⪤[RN,RP,f] L2 →
      ∀f2. f1 ~⊚ f2 ≘f → ⇩*[b,f1] L2 ≘ ⋆.
#RN #RP #b #f1 #L1 #H1 #Hf1 #f #L2 #H2 #f2 #H3
elim (sex_co_dropable_sn … H1 … H2 … H3) // -H1 -H2 -H3 -Hf1
#L #H #HL2 lapply (sex_inv_atom1 … H) -H //
qed-.

lemma sex_sdj_split_dx (R1) (R2) (RP):
      c_reflexive … R1 → c_reflexive … R2 → c_reflexive … RP →
      ∀L1,f1.
      (∀g,I,K,n. ⇩[n] L1 ≘ K.ⓘ[I] → ↑g = ⫰*[n] f1 → R_pw_confluent1_sex R1 R1 R2 cfull g K I) →
      ∀L2. L1 ⪤[R1,RP,f1] L2 → ∀f2. f1 ∥ f2 →
      ∃∃L. L1 ⪤[R2,cfull,f1] L & L ⪤[RP,R1,f2] L2.
#R1 #R2 #RP #HR1 #HR2 #HRP #L1 elim L1 -L1
[ #f1 #_ #L2 #H #f2 #_
  lapply (sex_inv_atom1 … H) -H #H destruct
  /2 width=3 by sex_atom, ex2_intro/
| #K1 #I1 #IH #f1 elim (pr_map_split_tl f1) * #g1 #H destruct
  #HR #L2 #H #f2 #Hf
  [ elim (sex_inv_push1 … H) -H #I2 #K2 #HK12 #HI12 #H destruct
    elim (pr_sdj_inv_push_sn … Hf ??) -Hf [1,3: * |*: // ] #g2 #Hg #H destruct
    elim (IH … HK12 … Hg) -IH -HK12 -Hg
    [1,3: /3 width=5 by sex_next, sex_push, ex2_intro/
    |2,4: /3 width=3 by drops_drop/
    ]
  | elim (sex_inv_next1 … H) -H #I2 #K2 #HK12 #HI12 #H destruct
    elim (pr_sdj_inv_next_sn … Hf ??) -Hf [|*: // ] #g2 #Hg #H destruct
    elim (IH … HK12 … Hg) -IH -HK12 -Hg
    [ /5 width=11 by sex_next, sex_push, drops_refl, ex2_intro/
    | /3 width=3 by drops_drop/
    ]
  ]
]
qed-.
