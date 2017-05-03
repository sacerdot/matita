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

include "ground_2/relocation/rtmap_sle.ma".
include "basic_2/notation/relations/relationstar_5.ma".
include "basic_2/syntax/lenv.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Basic_2A1: includes: lpx_sn_atom lpx_sn_pair *)
inductive lexs (RN,RP:relation3 lenv term term): rtmap → relation lenv ≝
| lexs_atom: ∀f. lexs RN RP f (⋆) (⋆)
| lexs_next: ∀f,I,L1,L2,V1,V2.
             lexs RN RP f L1 L2 → RN L1 V1 V2 →
             lexs RN RP (⫯f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
| lexs_push: ∀f,I,L1,L2,V1,V2.
             lexs RN RP f L1 L2 → RP L1 V1 V2 →
             lexs RN RP (↑f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation "generic entrywise extension (local environment)"
   'RelationStar RN RP f L1 L2 = (lexs RN RP f L1 L2).

definition R_pw_confluent2_lexs: relation3 lenv term term → relation3 lenv term term →
                                 relation3 lenv term term → relation3 lenv term term →
                                 relation3 lenv term term → relation3 lenv term term →
                                 relation3 rtmap lenv term ≝
                                 λR1,R2,RN1,RP1,RN2,RP2,f,L0,T0.
                                 ∀T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                                 ∀L1. L0 ⪤*[RN1, RP1, f] L1 → ∀L2. L0 ⪤*[RN2, RP2, f] L2 →
                                 ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

definition lexs_transitive: relation5 (relation3 lenv term term)
                                      (relation3 lenv term term) … ≝
                            λR1,R2,R3,RN,RP.
                            ∀f,L1,T1,T. R1 L1 T1 T → ∀L2. L1 ⪤*[RN, RP, f] L2 →
                            ∀T2. R2 L2 T T2 → R3 L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

fact lexs_inv_atom1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → X = ⋆ → Y = ⋆.
#RN #RP #f #X #Y * -f -X -Y //
#f #I #L1 #L2 #V1 #V2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom1 *)
lemma lexs_inv_atom1: ∀RN,RP,f,Y. ⋆ ⪤*[RN, RP, f] Y → Y = ⋆.
/2 width=6 by lexs_inv_atom1_aux/ qed-.

fact lexs_inv_next1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J,K1,W1. X = K1.ⓑ{J}W1 → f = ⫯g →
                         ∃∃K2,W2. K1 ⪤*[RN, RP, g] K2 & RN K1 W1 W2 & Y = K2.ⓑ{J}W2.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J #K1 #W1 #H destruct
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K1 #W1 #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #f #I #L1 #L2 #V1 #V2 #_ #_ #g #J #K1 #W1 #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair1 *)
lemma lexs_inv_next1: ∀RN,RP,g,J,K1,Y,W1. K1.ⓑ{J}W1 ⪤*[RN, RP, ⫯g] Y →
                      ∃∃K2,W2. K1 ⪤*[RN, RP, g] K2 & RN K1 W1 W2 & Y = K2.ⓑ{J}W2.
/2 width=7 by lexs_inv_next1_aux/ qed-.


fact lexs_inv_push1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J,K1,W1. X = K1.ⓑ{J}W1 → f = ↑g →
                         ∃∃K2,W2. K1 ⪤*[RN, RP, g] K2 & RP K1 W1 W2 & Y = K2.ⓑ{J}W2.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J #K1 #W1 #H destruct
| #f #I #L1 #L2 #V1 #V2 #_ #_ #g #J #K1 #W1 #_ #H elim (discr_next_push … H)
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K1 #W1 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push1: ∀RN,RP,g,J,K1,Y,W1. K1.ⓑ{J}W1 ⪤*[RN, RP, ↑g] Y →
                      ∃∃K2,W2. K1 ⪤*[RN, RP, g] K2 & RP K1 W1 W2 & Y = K2.ⓑ{J}W2.
/2 width=7 by lexs_inv_push1_aux/ qed-.

fact lexs_inv_atom2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → Y = ⋆ → X = ⋆.
#RN #RP #f #X #Y * -f -X -Y //
#f #I #L1 #L2 #V1 #V2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom2 *)
lemma lexs_inv_atom2: ∀RN,RP,f,X. X ⪤*[RN, RP, f] ⋆ → X = ⋆.
/2 width=6 by lexs_inv_atom2_aux/ qed-.

fact lexs_inv_next2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J,K2,W2. Y = K2.ⓑ{J}W2 → f = ⫯g →
                         ∃∃K1,W1. K1 ⪤*[RN, RP, g] K2 & RN K1 W1 W2 & X = K1.ⓑ{J}W1.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J #K2 #W2 #H destruct
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K2 #W2 #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #f #I #L1 #L2 #V1 #V2 #_ #_ #g #J #K2 #W2 #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair2 *)
lemma lexs_inv_next2: ∀RN,RP,g,J,X,K2,W2. X ⪤*[RN, RP, ⫯g] K2.ⓑ{J}W2 →
                      ∃∃K1,W1. K1 ⪤*[RN, RP, g] K2 & RN K1 W1 W2 & X = K1.ⓑ{J}W1.
/2 width=7 by lexs_inv_next2_aux/ qed-.

fact lexs_inv_push2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J,K2,W2. Y = K2.ⓑ{J}W2 → f = ↑g →
                         ∃∃K1,W1. K1 ⪤*[RN, RP, g] K2 & RP K1 W1 W2 & X = K1.ⓑ{J}W1.
#RN #RP #f #X #Y * -f -X -Y
[ #f #J #K2 #W2 #g #H destruct
| #f #I #L1 #L2 #V1 #V2 #_ #_ #g #J #K2 #W2 #_ #H elim (discr_next_push … H)
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K2 #W2 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push2: ∀RN,RP,g,J,X,K2,W2. X ⪤*[RN, RP, ↑g] K2.ⓑ{J}W2 →
                      ∃∃K1,W1. K1 ⪤*[RN, RP, g] K2 & RP K1 W1 W2 & X = K1.ⓑ{J}W1.
/2 width=7 by lexs_inv_push2_aux/ qed-.

(* Basic_2A1: includes lpx_sn_inv_pair *)
lemma lexs_inv_next: ∀RN,RP,f,I1,I2,L1,L2,V1,V2.
                     L1.ⓑ{I1}V1 ⪤*[RN, RP, ⫯f] (L2.ⓑ{I2}V2) →
                     ∧∧ L1 ⪤*[RN, RP, f] L2 & RN L1 V1 V2 & I1 = I2.
#RN #RP #f #I1 #I2 #L1 #L2 #V1 #V2 #H elim (lexs_inv_next1 … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

lemma lexs_inv_push: ∀RN,RP,f,I1,I2,L1,L2,V1,V2.
                     L1.ⓑ{I1}V1 ⪤*[RN, RP, ↑f] (L2.ⓑ{I2}V2) →
                     ∧∧ L1 ⪤*[RN, RP, f] L2 & RP L1 V1 V2 & I1 = I2.
#RN #RP #f #I1 #I2 #L1 #L2 #V1 #V2 #H elim (lexs_inv_push1 … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

lemma lexs_inv_tl: ∀RN,RP,f,I,L1,L2,V1,V2. L1 ⪤*[RN, RP, ⫱f] L2 →
                   RN L1 V1 V2 → RP L1 V1 V2 → 
                   L1.ⓑ{I}V1 ⪤*[RN, RP, f] L2.ⓑ{I}V2.
#RN #RP #f #I #L2 #L2 #V1 #V2 elim (pn_split f) *
/2 width=1 by lexs_next, lexs_push/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lexs_fwd_pair: ∀RN,RP,f,I1,I2,L1,L2,V1,V2. 
                     L1.ⓑ{I1}V1 ⪤*[RN, RP, f] L2.ⓑ{I2}V2 →
                     L1 ⪤*[RN, RP, ⫱f] L2 ∧ I1 = I2.
#RN #RP #f #I1 #I2 #L2 #L2 #V1 #V2 #Hf
elim (pn_split f) * #g #H destruct
[ elim (lexs_inv_push … Hf) | elim (lexs_inv_next … Hf) ] -Hf
/2 width=1 by conj/
qed-.

(* Basic properties *********************************************************)

lemma lexs_eq_repl_back: ∀RN,RP,L1,L2. eq_repl_back … (λf. L1 ⪤*[RN, RP, f] L2).
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I #L1 #L2 #V1 #v2 #_ #HV #IH #f2 #H
[ elim (eq_inv_nx … H) -H /3 width=3 by lexs_next/
| elim (eq_inv_px … H) -H /3 width=3 by lexs_push/
]
qed-.

lemma lexs_eq_repl_fwd: ∀RN,RP,L1,L2. eq_repl_fwd … (λf. L1 ⪤*[RN, RP, f] L2).
#RN #RP #L1 #L2 @eq_repl_sym /2 width=3 by lexs_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Basic_2A1: includes: lpx_sn_refl *)
lemma lexs_refl: ∀RN,RP.
                 (∀L. reflexive … (RN L)) →
                 (∀L. reflexive … (RP L)) →
                 ∀f.reflexive … (lexs RN RP f).
#RN #RP #HRN #HRP #f #L generalize in match f; -f elim L -L //
#L #I #V #IH * * /2 width=1 by lexs_next, lexs_push/
qed.

lemma lexs_sym: ∀RN,RP.
                (∀L1,L2,T1,T2. RN L1 T1 T2 → RN L2 T2 T1) →
                (∀L1,L2,T1,T2. RP L1 T1 T2 → RP L2 T2 T1) →
                ∀f. symmetric … (lexs RN RP f).
#RN #RP #HRN #HRP #f #L1 #L2 #H elim H -L1 -L2 -f
/3 width=2 by lexs_next, lexs_push/
qed-.

lemma lexs_pair_repl: ∀RN,RP,f,I,L1,L2,V1,V2.
                      L1.ⓑ{I}V1 ⪤*[RN, RP, f] L2.ⓑ{I}V2 →
                      ∀W1,W2. RN L1 W1 W2 → RP L1 W1 W2 →
                      L1.ⓑ{I}W1 ⪤*[RN, RP, f] L2.ⓑ{I}W2.
#RN #RP #f #I #L1 #L2 #V1 #V2 #HL12 #W1 #W2 #HN #HP
elim (lexs_fwd_pair … HL12) -HL12 /2 width=1 by lexs_inv_tl/
qed-.

lemma lexs_co: ∀RN1,RP1,RN2,RP2.
               (∀L1,T1,T2. RN1 L1 T1 T2 → RN2 L1 T1 T2) →
               (∀L1,T1,T2. RP1 L1 T1 T2 → RP2 L1 T1 T2) →
               ∀f,L1,L2. L1 ⪤*[RN1, RP1, f] L2 → L1 ⪤*[RN2, RP2, f] L2.
#RN1 #RP1 #RN2 #RP2 #HRN #HRP #f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by lexs_atom, lexs_next, lexs_push/
qed-.

lemma lexs_co_isid: ∀RN1,RP1,RN2,RP2.
                    (∀L1,T1,T2. RP1 L1 T1 T2 → RP2 L1 T1 T2) →
                    ∀f,L1,L2. L1 ⪤*[RN1, RP1, f] L2 → 𝐈⦃f⦄ →
                    L1 ⪤*[RN2, RP2, f] L2.
#RN1 #RP1 #RN2 #RP2 #HR #f #L1 #L2 #H elim H -f -L1 -L2 //
#f #I #K1 #K2 #V1 #V2 #_ #HV12 #IH #H
[ elim (isid_inv_next … H) -H //
| /4 width=3 by lexs_push, isid_inv_push/
] 
qed-.

lemma sle_lexs_trans: ∀RN,RP. (∀L,T1,T2. RN L T1 T2 → RP L T1 T2) →
                      ∀f2,L1,L2. L1 ⪤*[RN, RP, f2] L2 →
                      ∀f1. f1 ⊆ f2 → L1 ⪤*[RN, RP, f1] L2.
#RN #RP #HR #f2 #L1 #L2 #H elim H -f2 -L1 -L2 //
#f2 #I #L1 #L2 #V1 #V2 #_ #HV12 #IH
[ * * [2: #n1 ] ] #f1 #H
[ /4 width=5 by lexs_next, sle_inv_nn/
| /4 width=5 by lexs_push, sle_inv_pn/
| elim (sle_inv_xp … H) -H [2,3: // ]
  #g1 #H #H1 destruct /3 width=5 by lexs_push/
]
qed-.

lemma sle_lexs_conf: ∀RN,RP. (∀L,T1,T2. RP L T1 T2 → RN L T1 T2) →
                     ∀f1,L1,L2. L1 ⪤*[RN, RP, f1] L2 →
                     ∀f2. f1 ⊆ f2 → L1 ⪤*[RN, RP, f2] L2.
#RN #RP #HR #f1 #L1 #L2 #H elim H -f1 -L1 -L2 //
#f1 #I #L1 #L2 #V1 #V2 #_ #HV12 #IH
[2: * * [2: #n2 ] ] #f2 #H
[ /4 width=5 by lexs_next, sle_inv_pn/
| /4 width=5 by lexs_push, sle_inv_pp/
| elim (sle_inv_nx … H) -H [2,3: // ]
  #g2 #H #H2 destruct /3 width=5 by lexs_next/
]
qed-.

lemma lexs_sle_split: ∀R1,R2,RP. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                      ∀f,L1,L2. L1 ⪤*[R1, RP, f] L2 → ∀g. f ⊆ g →
                      ∃∃L. L1 ⪤*[R1, RP, g] L & L ⪤*[R2, cfull, f] L2.
#R1 #R2 #RP #HR1 #HR2 #f #L1 #L2 #H elim H -f -L1 -L2
[ /2 width=3 by lexs_atom, ex2_intro/ ]
#f #I #L1 #L2 #V1 #V2 #_ #HV12 #IH #y #H
[ elim (sle_inv_nx … H ??) -H [ |*: // ] #g #Hfg #H destruct
  elim (IH … Hfg) -IH -Hfg /3 width=5 by lexs_next, ex2_intro/
| elim (sle_inv_px … H ??) -H [1,3: * |*: // ] #g #Hfg #H destruct
  elim (IH … Hfg) -IH -Hfg /3 width=5 by lexs_next, lexs_push, ex2_intro/
]
qed-.

lemma lexs_dec: ∀RN,RP.
                (∀L,T1,T2. Decidable (RN L T1 T2)) →
                (∀L,T1,T2. Decidable (RP L T1 T2)) →
                ∀L1,L2,f. Decidable (L1 ⪤*[RN, RP, f] L2).
#RN #RP #HRN #HRP #L1 elim L1 -L1 [ * | #L1 #I1 #V1 #IH * ]
[ /2 width=1 by lexs_atom, or_introl/
| #L2 #I2 #V2 #f @or_intror #H
  lapply (lexs_inv_atom1 … H) -H #H destruct
| #f @or_intror #H
  lapply (lexs_inv_atom2 … H) -H #H destruct
| #L2 #I2 #V2 #f elim (eq_bind2_dec I1 I2) #H destruct
  [2: @or_intror #H elim (lexs_fwd_pair … H) -H /2 width=1 by/ ]
  elim (IH L2 (⫱f)) -IH #HL12
  [2: @or_intror #H elim (lexs_fwd_pair … H) -H /2 width=1 by/ ]
  elim (pn_split f) * #g #H destruct
  [ elim (HRP L1 V1 V2) | elim (HRN L1 V1 V2) ] -HRP -HRN #HV12
  [1,3: /3 width=1 by lexs_push, lexs_next, or_introl/ ]
  @or_intror #H
  [ elim (lexs_inv_push … H) | elim (lexs_inv_next … H) ] -H
  /2 width=1 by/
]
qed-.
