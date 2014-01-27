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

include "basic_2/substitution/lleq_ext.ma".
include "basic_2/computation/lpxs_ldrop.ma".
include "basic_2/computation/lpxs_cpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS ******************)

(* Advanced properties ******************************************************)

fact le_repl_sn_aux: ∀x,y,z:nat. x ≤ z → x = y → y ≤ z.
// qed-.

fact pippo_aux: ∀h,g,G,L1,T,T1,d,e. ⦃G, L1⦄ ⊢ T ▶×[d, e] T1 → e = ∞ →
                ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                ∃∃T2. ⦃G, L2⦄ ⊢ T ▶×[d, e] T2 & ⦃G, L1⦄ ⊢ T1 ➡*[h, g] T2 &
                      L1 ⋕[T, d] L2 ↔ T1 = T2.
#h #g #G #L1 #T #T1 #d #e #H elim H -G -L1 -T -T1 -d -e [ * ]
[ /5 width=5 by lpxs_fwd_length, lleq_sort, ex3_intro, conj/
| #i #G #L1 elim (lt_or_ge i (|L1|)) [2: /6 width=6 by lpxs_fwd_length, lleq_free, le_repl_sn_aux, ex3_intro, conj/ ]
  #Hi #d elim (ylt_split i d) [ /5 width=5 by lpxs_fwd_length, lleq_skip, ex3_intro, conj/ ]
  #Hdi #e #He #L2 elim (lleq_dec (#i) L1 L2 d) [ /4 width=5 by lpxs_fwd_length, ex3_intro, conj/ ]
  #HnL12 #HL12 elim (ldrop_O1_lt L1 i) // -Hi #I #K1 #V1 #HLK1
  elim (lpxs_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpxs_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  elim (lift_total V2 0 (i+1)) #W2 #HVW2
  @(ex3_intro … W2) /2 width=7 by cpxs_delta, cpy_subst/ -I -K1 -V1 -Hdi
  @conj #H [ elim HnL12 // | destruct elim (lift_inv_lref2_be … HVW2) // ]
| /5 width=5 by lpxs_fwd_length, lleq_gref, ex3_intro, conj/
| #I #G #L1 #K1 #V1 #W1 #i #d #e #Hdi #Hide #HLK1 #HVW1 #He #L2 #HL12 destruct
  elim (lpxs_ldrop_conf … HLK1 … HL12) -HL12 #X #H #HLK2
  elim (lpxs_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (ldrop_fwd_drop2 … HLK1) -HLK1 #HLK1
  elim (lift_total V2 0 (i+1)) #W2 #HVW2
  @(ex3_intro … W2) /2 width=10 by cpxs_lift, cpy_subst/
  
  
  elim (lleq_dec (#i) L1 L2 d) 
    
|
]  

axiom lleq_lpxs_trans: ∀h,g,G,L1,L2,T,d. L1 ⋕[T, d] L2 → ∀K2. ⦃G, L2⦄ ⊢ ➡*[h, g] K2 →
                       ∃∃K1. ⦃G, L1⦄ ⊢ ➡*[h, g] K1 & K1 ⋕[T, d] K2.
(*
#h #g #G #L1 #L2 #T #d #H @(lleq_ind_alt … H) -L1 -L2 -T -d
[
|
|
|
|
| #a #I #L1 #L2 #V #T #d #_ #_ #IHV #IHT #K2 #HLK2
  elim (IHV … HLK2) -IHV #KV #HLKV #HV
  elim (IHT (K2.ⓑ{I}V)) -IHT /2 width=1 by lpxs_pair_refl/ -HLK2 #Y #H #HT
  elim (lpxs_inv_pair1 … H) -H #KT #VT #HLKT #_ #H destruct  

#h #g #G #L1 #L2 #T #d * #HL12 #IH #K2 #HLK2
*)

(* Properties on lazy equivalence for local environments ********************)

lemma lpxs_lleq_fqu_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                           ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 → K1 ⋕[T1, 0] L1 →
                           ∃∃K2. ⦃G1, K1, T1⦄ ⊃ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 & K2 ⋕[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G1 #L1 #V1 #X #H1 #H2 elim (lpxs_inv_pair2 … H1) -H1
  #K0 #V0 #H1KL1 #_ #H destruct
  elim (lleq_inv_lref_ge_dx … H2 ? I L1 V1) -H2 //
  #I1 #K1 #H #H2KL1 lapply (ldrop_inv_O2 … H) -H #H destruct
  /2 width=4 by fqu_lref_O, ex3_intro/
| * [ #a ] #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H
  [ elim (lleq_inv_bind … H)
  | elim (lleq_inv_flat … H)
  ] -H /2 width=4 by fqu_pair_sn, ex3_intro/
| #a #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=4 by lpxs_pair, fqu_bind_dx, ex3_intro/
| #I #G1 #L1 #V1 #T1 #K1 #HLK1 #H elim (lleq_inv_flat … H) -H
  /2 width=4 by fqu_flat_dx, ex3_intro/
| #G1 #L1 #L #T1 #U1 #e #HL1 #HTU1 #K1 #H1KL1 #H2KL1
  elim (ldrop_O1_le (e+1) K1)
  [ #K #HK1 lapply (lleq_inv_lift_le … H2KL1 … HK1 HL1 … HTU1 ?) -H2KL1 //
    #H2KL elim (lpxs_ldrop_trans_O1 … H1KL1 … HL1) -L1
    #K0 #HK10 #H1KL lapply (ldrop_mono … HK10 … HK1) -HK10 #H destruct
    /3 width=4 by fqu_drop, ex3_intro/
  | lapply (ldrop_fwd_length_le2 … HL1) -L -T1 -g
    lapply (lleq_fwd_length … H2KL1) //
  ]
]
qed-.

lemma lpxs_lleq_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 → K1 ⋕[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊃⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 & K2 ⋕[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fquq_inv_gen … H) -H
[ #H elim (lpxs_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.

lemma lpxs_lleq_fqup_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 → K1 ⋕[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊃+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 & K2 ⋕[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H #K1 #H1KL1 #H2KL1 elim (lpxs_lleq_fqu_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G2 #L #L2 #T #T2 #_ #HT2 #IHT1 #K1 #H1KL1 #H2KL1 elim (IHT1 … H2KL1) // -L1
  #K #HT1 #H1KL #H2KL elim (lpxs_lleq_fqu_trans … HT2 … H1KL H2KL) -L
  /3 width=5 by fqup_strap1, ex3_intro/
]
qed-.

lemma lpxs_lleq_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                            ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 → K1 ⋕[T1, 0] L1 →
                            ∃∃K2. ⦃G1, K1, T1⦄ ⊃* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2 & K2 ⋕[T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #H1KL1 #H2KL1
elim (fqus_inv_gen … H) -H
[ #H elim (lpxs_lleq_fqup_trans … H … H1KL1 H2KL1) -L1
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /2 width=4 by ex3_intro/
]
qed-.
