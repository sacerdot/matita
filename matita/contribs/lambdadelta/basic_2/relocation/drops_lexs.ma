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

include "basic_2/relocation/drops.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties on general entrywise extension of context-sensitive relations *)

(* Basic_2A1: includes: lpx_sn_deliftable_dropable *)
lemma lexs_deliftable_dropable: ∀RN,RP. d_deliftable2_sn RN → d_deliftable2_sn RP →
                                dropable_sn (lexs RN RP).
#RN #RP #HN #HP #L1 #K1 #c #f #H elim H -L1 -K1 -f
[ #f #Hf #X #f2 #H #f1 #Hf2 >(lexs_inv_atom1 … H) -X
  /4 width=3 by lexs_atom, drops_atom, ex2_intro/
| #I #L1 #K1 #V1 #f #_ #IH #X #f2 #H #f1 #Hf2 elim (after_inv_nxx … Hf2) -Hf2 [2,3: // ]
  #g2 #Hg2 #H2 destruct elim (lexs_inv_next1 … H) -H
  #L2 #V2 #HL12 #HV12 #H destruct elim (IH … HL12 … Hg2) -g2
  /3 width=3 by drops_drop, ex2_intro/
| #I #L1 #K1 #V1 #W1 #f #HLK #HWV #IH #X #f2 #H #f1 #Hf2 elim (after_inv_pxx … Hf2) -Hf2 [1,3:* |*: // ]
  #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (lexs_inv_push1 … H) | elim (lexs_inv_next1 … H) ] -H
  #L2 #V2 #HL12 #HV12 #H destruct elim (IH … HL12 … Hg2) -g2
  [ elim (HP … HV12 … HLK … HWV) | elim (HN … HV12 … HLK … HWV) ] -V1
  /3 width=5 by lexs_next, lexs_push, drops_skip, ex2_intro/
]
qed-.

(* Basic_2A1: includes: lpx_sn_liftable_dedropable *)
lemma lexs_liftable_dedropable: ∀RN,RP. (∀L. reflexive ? (RN L)) → (∀L. reflexive ? (RP L)) →
                                d_liftable2 RN → d_liftable2 RP → dedropable_sn (lexs RN RP).
#RN #RP #H1RN #H1RP #H2RN #H2RP #L1 #K1 #c #f #H elim H -L1 -K1 -f
[ #f #Hf #X #f1 #H #f2 #Hf2 >(lexs_inv_atom1 … H) -X
  /4 width=4 by drops_atom, lexs_atom, ex3_intro/
| #I #L1 #K1 #V1 #f #_ #IHLK1 #K2 #f1 #HK12 #f2 #Hf2
  elim (after_inv_nxx … Hf2) -Hf2 [2,3: // ] #g2 #Hg2 #H destruct
  elim (IHLK1 … HK12 … Hg2) -K1
  /3 width=6 by drops_drop, lexs_next, ex3_intro/
| #I #L1 #K1 #V1 #W1 #f #HLK1 #HWV1 #IHLK1 #X #f1 #H #f2 #Hf2
  elim (after_inv_pxx … Hf2) -Hf2 [1,3: * |*: // ] #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (lexs_inv_push1 … H) | elim (lexs_inv_next1 … H) ] -H #K2 #W2 #HK12 #HW12 #H destruct
  [ elim (H2RP … HW12 … HLK1 … HWV1) | elim (H2RN … HW12 … HLK1 … HWV1) ] -W1
  elim (IHLK1 … HK12 … Hg2) -K1
  /3 width=6 by drops_skip, lexs_next, lexs_push, ex3_intro/
]
qed-.

fact lexs_dropable_aux: ∀RN,RP,L2,K2,c,f. ⬇*[c, f] L2 ≡ K2 → 𝐔⦃f⦄ →
                        ∀L1,f2. L1 ⦻*[RN, RP, f2] L2 → ∀f1. f ⊚ f1 ≡ f2 →
                        ∃∃K1. ⬇*[c, f] L1 ≡ K1 & K1 ⦻*[RN, RP, f1] K2.
#RN #RP #L2 #K2 #c #f #H elim H -L2 -K2 -f
[ #f #Hf #_ #X #f2 #H #f1 #Hf2 lapply (lexs_inv_atom2 … H) -H
  #H destruct /4 width=3 by lexs_atom, drops_atom, ex2_intro/
| #I #L2 #K2 #V2 #f #_ #IH #Hf #X #f2 #HX #f1 #Hf2
  elim (after_inv_nxx … Hf2) -Hf2 [2,3: // ] #g2 #Hg2 #H destruct
  elim (lexs_inv_next2 … HX) -HX #L1 #V1 #HL12 #HV12 #H destruct
  elim (IH … HL12 … Hg2) -L2 -V2 -g2
  /3 width=3 by drops_drop, isuni_inv_next, ex2_intro/
| #I #L2 #K2 #V2 #W2 #f #_ #HWV2 #IH #Hf #X #f2 #HX #f1 #Hf2
  elim (after_inv_pxx … Hf2) -Hf2 [1,3: * |*: // ] #g1 #g2 #Hg2 #H1 #H2 destruct
  [ elim (lexs_inv_push2 … HX) | elim (lexs_inv_next2 … HX) ] -HX #L1 #V1 #HL12 #HV12 #H destruct
  elim (IH … HL12 … Hg2) -L2 -g2 /2 width=3 by isuni_fwd_push/ #K1 #HLK1 #HK12
  lapply (isuni_inv_push … Hf ??) -Hf [3,6: |*: // ] #Hf
  lapply (lifts_fwd_isid … HWV2 … Hf) #H destruct -HWV2
  lapply (drops_fwd_isid … HLK1 … Hf) #H destruct -HLK1
  /4 width=5 by lexs_next, lexs_push, drops_refl, isid_push, ex2_intro/
]
qed-.

(* Basic_2A1: includes: lpx_sn_dropable *)
lemma lexs_dropable: ∀RN,RP. dropable_dx (lexs RN RP).
/2 width=5 by lexs_dropable_aux/ qed-.

(* Basic_2A1: includes: lpx_sn_drop_conf *)
lemma lexs_drops_conf_next: ∀RN,RP. d_deliftable2_sn RN → d_deliftable2_sn RP →
                            ∀L1,L2,f2. L1 ⦻*[RN, RP, f2] L2 →
                            ∀I,K1,V1,c,f. ⬇*[c,f] L1 ≡ K1.ⓑ{I}V1 →
                            ∀f1. f ⊚ ⫯f1 ≡ f2 →
                            ∃∃K2,V2. ⬇*[c,f] L2 ≡ K2.ⓑ{I}V2 & K1 ⦻*[RN, RP, f1] K2 & RN K1 V1 V2.
#RN #RP #HRN #HRP #L1 #L2 #f2 #HL12 #I #K1 #V1 #c #f #HLK1 #f1 #Hf2
elim (lexs_deliftable_dropable … HRN HRP … HLK1 … HL12 … Hf2) -L1 -f2 -HRN -HRP
#X #HX #HLK2 elim (lexs_inv_next1 … HX) -HX
#K2 #V2 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma lexs_drops_conf_push: ∀RN,RP. d_deliftable2_sn RN → d_deliftable2_sn RP →
                            ∀L1,L2,f2. L1 ⦻*[RN, RP, f2] L2 →
                            ∀I,K1,V1,c,f. ⬇*[c,f] L1 ≡ K1.ⓑ{I}V1 →
                            ∀f1. f ⊚ ↑f1 ≡ f2 →
                            ∃∃K2,V2. ⬇*[c,f] L2 ≡ K2.ⓑ{I}V2 & K1 ⦻*[RN, RP, f1] K2 & RP K1 V1 V2.
#RN #RP #HRN #HRP #L1 #L2 #f2 #HL12 #I #K1 #V1 #c #f #HLK1 #f1 #Hf2
elim (lexs_deliftable_dropable … HRN HRP … HLK1 … HL12 … Hf2) -L1 -f2 -HRN -HRP
#X #HX #HLK2 elim (lexs_inv_push1 … HX) -HX
#K2 #V2 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

(* Basic_2A1: includes: lpx_sn_drop_trans *)
lemma lexs_drops_trans_next: ∀RN,RP,L1,L2,f2. L1 ⦻*[RN, RP, f2] L2 →
                             ∀I,K2,V2,c,f. ⬇*[c,f] L2 ≡ K2.ⓑ{I}V2 → 𝐔⦃f⦄ →
                             ∀f1. f ⊚ ⫯f1 ≡ f2 →
                             ∃∃K1,V1. ⬇*[c,f] L1 ≡ K1.ⓑ{I}V1 & K1 ⦻*[RN, RP, f1] K2 & RN K1 V1 V2.
#RN #RP #L1 #L2 #f2 #HL12 #I #K1 #V1 #c #f #HLK1 #Hf #f1 #Hf2
elim (lexs_dropable … HL12 … HLK1 … Hf … Hf2) -L2 -f2 -Hf
#X #HLK1 #HX elim (lexs_inv_next2 … HX) -HX
#K1 #V1 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma lexs_drops_trans_push: ∀RN,RP,L1,L2,f2. L1 ⦻*[RN, RP, f2] L2 →
                             ∀I,K2,V2,c,f. ⬇*[c,f] L2 ≡ K2.ⓑ{I}V2 → 𝐔⦃f⦄ →
                             ∀f1. f ⊚ ↑f1 ≡ f2 →
                             ∃∃K1,V1. ⬇*[c,f] L1 ≡ K1.ⓑ{I}V1 & K1 ⦻*[RN, RP, f1] K2 & RP K1 V1 V2.
#RN #RP #L1 #L2 #f2 #HL12 #I #K1 #V1 #c #f #HLK1 #Hf #f1 #Hf2
elim (lexs_dropable … HL12 … HLK1 … Hf … Hf2) -L2 -f2 -Hf
#X #HLK1 #HX elim (lexs_inv_push2 … HX) -HX
#K1 #V1 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma drops_lexs_trans_next: ∀RN,RP. (∀L. reflexive ? (RN L)) → (∀L. reflexive ? (RP L)) →
                             d_liftable2 RN → d_liftable2 RP →
                             ∀K1,K2,f1. K1 ⦻*[RN, RP, f1] K2 →
                             ∀I,L1,V1,c,f. ⬇*[c,f] L1.ⓑ{I}V1 ≡ K1 →
                             ∀f2. f ⊚ f1 ≡ ⫯f2 →
                             ∃∃L2,V2. ⬇*[c,f] L2.ⓑ{I}V2 ≡ K2 & L1 ⦻*[RN, RP, f2] L2 & RN L1 V1 V2 & L1.ⓑ{I}V1≡[f]L2.ⓑ{I}V2.
#RN #RP #H1RN #H1RP #H2RN #H2RP #K1 #K2 #f1 #HK12 #I #L1 #V1 #c #f #HLK1 #f2 #Hf2
elim (lexs_liftable_dedropable … H1RN H1RP H2RN H2RP … HLK1 … HK12 … Hf2) -K1 -f1 -H1RN -H1RP -H2RN -H2RP
#X #HX #HLK2 #H1L12 elim (lexs_inv_next1 … HX) -HX
#L2 #V2 #H2L12 #HV12 #H destruct /2 width=6 by ex4_2_intro/
qed-.

lemma drops_lexs_trans_push: ∀RN,RP. (∀L. reflexive ? (RN L)) → (∀L. reflexive ? (RP L)) →
                             d_liftable2 RN → d_liftable2 RP →
                             ∀K1,K2,f1. K1 ⦻*[RN, RP, f1] K2 →
                             ∀I,L1,V1,c,f. ⬇*[c,f] L1.ⓑ{I}V1 ≡ K1 →
                             ∀f2. f ⊚ f1 ≡ ↑f2 →
                             ∃∃L2,V2. ⬇*[c,f] L2.ⓑ{I}V2 ≡ K2 & L1 ⦻*[RN, RP, f2] L2 & RP L1 V1 V2 & L1.ⓑ{I}V1≡[f]L2.ⓑ{I}V2.
#RN #RP #H1RN #H1RP #H2RN #H2RP #K1 #K2 #f1 #HK12 #I #L1 #V1 #c #f #HLK1 #f2 #Hf2
elim (lexs_liftable_dedropable … H1RN H1RP H2RN H2RP … HLK1 … HK12 … Hf2) -K1 -f1 -H1RN -H1RP -H2RN -H2RP
#X #HX #HLK2 #H1L12 elim (lexs_inv_push1 … HX) -HX
#L2 #V2 #H2L12 #HV12 #H destruct /2 width=6 by ex4_2_intro/
qed-.
