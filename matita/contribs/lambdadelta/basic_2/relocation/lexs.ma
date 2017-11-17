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

inductive lexs (RN,RP:relation3 lenv bind bind): rtmap → relation lenv ≝
| lexs_atom: ∀f. lexs RN RP f (⋆) (⋆)
| lexs_next: ∀f,I1,I2,L1,L2.
             lexs RN RP f L1 L2 → RN L1 I1 I2 →
             lexs RN RP (⫯f) (L1.ⓘ{I1}) (L2.ⓘ{I2})
| lexs_push: ∀f,I1,I2,L1,L2.
             lexs RN RP f L1 L2 → RP L1 I1 I2 →
             lexs RN RP (↑f) (L1.ⓘ{I1}) (L2.ⓘ{I2})
.

interpretation "generic entrywise extension (local environment)"
   'RelationStar RN RP f L1 L2 = (lexs RN RP f L1 L2).

definition R_pw_confluent2_lexs: relation3 lenv bind bind → relation3 lenv bind bind →
                                 relation3 lenv bind bind → relation3 lenv bind bind →
                                 relation3 lenv bind bind → relation3 lenv bind bind →
                                 relation3 rtmap lenv bind ≝
                                 λR1,R2,RN1,RP1,RN2,RP2,f,L0,T0.
                                 ∀T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                                 ∀L1. L0 ⪤*[RN1, RP1, f] L1 → ∀L2. L0 ⪤*[RN2, RP2, f] L2 →
                                 ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

definition lexs_transitive: relation5 (relation3 lenv bind bind)
                                      (relation3 lenv bind bind) … ≝
                            λR1,R2,R3,RN,RP.
                            ∀f,L1,T1,T. R1 L1 T1 T → ∀L2. L1 ⪤*[RN, RP, f] L2 →
                            ∀T2. R2 L2 T T2 → R3 L1 T1 T2.

(* Basic inversion lemmas ***************************************************)

fact lexs_inv_atom1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → X = ⋆ → Y = ⋆.
#RN #RP #f #X #Y * -f -X -Y //
#f #I1 #I2 #L1 #L2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom1 *)
lemma lexs_inv_atom1: ∀RN,RP,f,Y. ⋆ ⪤*[RN, RP, f] Y → Y = ⋆.
/2 width=6 by lexs_inv_atom1_aux/ qed-.

fact lexs_inv_next1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J1,K1. X = K1.ⓘ{J1} → f = ⫯g →
                         ∃∃J2,K2. K1 ⪤*[RN, RP, g] K2 & RN K1 J1 J2 & Y = K2.ⓘ{J2}.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J1 #K1 #H destruct
| #f #I1 #I2 #L1 #L2 #HL #HI #g #J1 #K1 #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #f #I1 #I2 #L1 #L2 #_ #_ #g #J1 #K1 #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair1 *)
lemma lexs_inv_next1: ∀RN,RP,g,J1,K1,Y. K1.ⓘ{J1} ⪤*[RN, RP, ⫯g] Y →
                      ∃∃J2,K2. K1 ⪤*[RN, RP, g] K2 & RN K1 J1 J2 & Y = K2.ⓘ{J2}.
/2 width=7 by lexs_inv_next1_aux/ qed-.

fact lexs_inv_push1_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J1,K1. X = K1.ⓘ{J1} → f = ↑g →
                         ∃∃J2,K2. K1 ⪤*[RN, RP, g] K2 & RP K1 J1 J2 & Y = K2.ⓘ{J2}.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J1 #K1 #H destruct
| #f #I1 #I2 #L1 #L2 #_ #_ #g #J1 #K1 #_ #H elim (discr_next_push … H)
| #f #I1 #I2 #L1 #L2 #HL #HI #g #J1 #K1 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push1: ∀RN,RP,g,J1,K1,Y. K1.ⓘ{J1} ⪤*[RN, RP, ↑g] Y →
                      ∃∃J2,K2. K1 ⪤*[RN, RP, g] K2 & RP K1 J1 J2 & Y = K2.ⓘ{J2}.
/2 width=7 by lexs_inv_push1_aux/ qed-.

fact lexs_inv_atom2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → Y = ⋆ → X = ⋆.
#RN #RP #f #X #Y * -f -X -Y //
#f #I1 #I2 #L1 #L2 #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom2 *)
lemma lexs_inv_atom2: ∀RN,RP,f,X. X ⪤*[RN, RP, f] ⋆ → X = ⋆.
/2 width=6 by lexs_inv_atom2_aux/ qed-.

fact lexs_inv_next2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J2,K2. Y = K2.ⓘ{J2} → f = ⫯g →
                         ∃∃J1,K1. K1 ⪤*[RN, RP, g] K2 & RN K1 J1 J2 & X = K1.ⓘ{J1}.
#RN #RP #f #X #Y * -f -X -Y
[ #f #g #J2 #K2 #H destruct
| #f #I1 #I2 #L1 #L2 #HL #HI #g #J2 #K2 #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #f #I1 #I2 #L1 #L2 #_ #_ #g #J2 #K2 #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair2 *)
lemma lexs_inv_next2: ∀RN,RP,g,J2,X,K2. X ⪤*[RN, RP, ⫯g] K2.ⓘ{J2} →
                      ∃∃J1,K1. K1 ⪤*[RN, RP, g] K2 & RN K1 J1 J2 & X = K1.ⓘ{J1}.
/2 width=7 by lexs_inv_next2_aux/ qed-.

fact lexs_inv_push2_aux: ∀RN,RP,f,X,Y. X ⪤*[RN, RP, f] Y → ∀g,J2,K2. Y = K2.ⓘ{J2} → f = ↑g →
                         ∃∃J1,K1. K1 ⪤*[RN, RP, g] K2 & RP K1 J1 J2 & X = K1.ⓘ{J1}.
#RN #RP #f #X #Y * -f -X -Y
[ #f #J2 #K2 #g #H destruct
| #f #I1 #I2 #L1 #L2 #_ #_ #g #J2 #K2 #_ #H elim (discr_next_push … H)
| #f #I1 #I2 #L1 #L2 #HL #HI #g #J2 #K2 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push2: ∀RN,RP,g,J2,X,K2. X ⪤*[RN, RP, ↑g] K2.ⓘ{J2} →
                      ∃∃J1,K1. K1 ⪤*[RN, RP, g] K2 & RP K1 J1 J2 & X = K1.ⓘ{J1}.
/2 width=7 by lexs_inv_push2_aux/ qed-.

(* Basic_2A1: includes lpx_sn_inv_pair *)
lemma lexs_inv_next: ∀RN,RP,f,I1,I2,L1,L2.
                     L1.ⓘ{I1} ⪤*[RN, RP, ⫯f] L2.ⓘ{I2} →
                     L1 ⪤*[RN, RP, f] L2 ∧ RN L1 I1 I2.
#RN #RP #f #I1 #I2 #L1 #L2 #H elim (lexs_inv_next1 … H) -H
#I0 #L0 #HL10 #HI10 #H destruct /2 width=1 by conj/
qed-.

lemma lexs_inv_push: ∀RN,RP,f,I1,I2,L1,L2.
                     L1.ⓘ{I1} ⪤*[RN, RP, ↑f] L2.ⓘ{I2} →
                     L1 ⪤*[RN, RP, f] L2 ∧ RP L1 I1 I2.
#RN #RP #f #I1 #I2 #L1 #L2 #H elim (lexs_inv_push1 … H) -H
#I0 #L0 #HL10 #HI10 #H destruct /2 width=1 by conj/
qed-.

lemma lexs_inv_tl: ∀RN,RP,f,I1,I2,L1,L2. L1 ⪤*[RN, RP, ⫱f] L2 →
                   RN L1 I1 I2 → RP L1 I1 I2 → 
                   L1.ⓘ{I1} ⪤*[RN, RP, f] L2.ⓘ{I2}.
#RN #RP #f #I1 #I2 #L2 #L2 elim (pn_split f) *
/2 width=1 by lexs_next, lexs_push/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lexs_fwd_bind: ∀RN,RP,f,I1,I2,L1,L2. 
                     L1.ⓘ{I1} ⪤*[RN, RP, f] L2.ⓘ{I2} →
                     L1 ⪤*[RN, RP, ⫱f] L2.
#RN #RP #f #I1 #I2 #L1 #L2 #Hf
elim (pn_split f) * #g #H destruct
[ elim (lexs_inv_push … Hf) | elim (lexs_inv_next … Hf) ] -Hf //
qed-.

(* Basic properties *********************************************************)

lemma lexs_eq_repl_back: ∀RN,RP,L1,L2. eq_repl_back … (λf. L1 ⪤*[RN, RP, f] L2).
#RN #RP #L1 #L2 #f1 #H elim H -f1 -L1 -L2 //
#f1 #I1 #I2 #L1 #L2 #_ #HI #IH #f2 #H
[ elim (eq_inv_nx … H) -H /3 width=3 by lexs_next/
| elim (eq_inv_px … H) -H /3 width=3 by lexs_push/
]
qed-.

lemma lexs_eq_repl_fwd: ∀RN,RP,L1,L2. eq_repl_fwd … (λf. L1 ⪤*[RN, RP, f] L2).
#RN #RP #L1 #L2 @eq_repl_sym /2 width=3 by lexs_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Basic_2A1: uses: lpx_sn_refl *)
lemma lexs_refl: ∀RN,RP.
                 (∀L. reflexive … (RN L)) →
                 (∀L. reflexive … (RP L)) →
                 ∀f.reflexive … (lexs RN RP f).
#RN #RP #HRN #HRP #f #L generalize in match f; -f elim L -L //
#L #I #IH #f elim (pn_split f) *
#g #H destruct /2 width=1 by lexs_next, lexs_push/
qed.

lemma lexs_sym: ∀RN,RP.
                (∀L1,L2,I1,I2. RN L1 I1 I2 → RN L2 I2 I1) →
                (∀L1,L2,I1,I2. RP L1 I1 I2 → RP L2 I2 I1) →
                ∀f. symmetric … (lexs RN RP f).
#RN #RP #HRN #HRP #f #L1 #L2 #H elim H -L1 -L2 -f
/3 width=2 by lexs_next, lexs_push/
qed-.

lemma lexs_pair_repl: ∀RN,RP,f,I1,I2,L1,L2.
                      L1.ⓘ{I1} ⪤*[RN, RP, f] L2.ⓘ{I2} →
                      ∀J1,J2. RN L1 J1 J2 → RP L1 J1 J2 →
                      L1.ⓘ{J1} ⪤*[RN, RP, f] L2.ⓘ{J2}.
/3 width=3 by lexs_inv_tl, lexs_fwd_bind/ qed-.

lemma lexs_co: ∀RN1,RP1,RN2,RP2.
               (∀L1,I1,I2. RN1 L1 I1 I2 → RN2 L1 I1 I2) →
               (∀L1,I1,I2. RP1 L1 I1 I2 → RP2 L1 I1 I2) →
               ∀f,L1,L2. L1 ⪤*[RN1, RP1, f] L2 → L1 ⪤*[RN2, RP2, f] L2.
#RN1 #RP1 #RN2 #RP2 #HRN #HRP #f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by lexs_atom, lexs_next, lexs_push/
qed-.

lemma lexs_co_isid: ∀RN1,RP1,RN2,RP2.
                    (∀L1,I1,I2. RP1 L1 I1 I2 → RP2 L1 I1 I2) →
                    ∀f,L1,L2. L1 ⪤*[RN1, RP1, f] L2 → 𝐈⦃f⦄ →
                    L1 ⪤*[RN2, RP2, f] L2.
#RN1 #RP1 #RN2 #RP2 #HR #f #L1 #L2 #H elim H -f -L1 -L2 //
#f #I1 #I2 #K1 #K2 #_ #HI12 #IH #H
[ elim (isid_inv_next … H) -H //
| /4 width=3 by lexs_push, isid_inv_push/
]
qed-.

lemma sle_lexs_trans: ∀RN,RP. (∀L,I1,I2. RN L I1 I2 → RP L I1 I2) →
                      ∀f2,L1,L2. L1 ⪤*[RN, RP, f2] L2 →
                      ∀f1. f1 ⊆ f2 → L1 ⪤*[RN, RP, f1] L2.
#RN #RP #HR #f2 #L1 #L2 #H elim H -f2 -L1 -L2 //
#f2 #I1 #I2 #L1 #L2 #_ #HI12 #IH #f1 #H12
[ elim (pn_split f1) * ]
[ /4 width=5 by lexs_push, sle_inv_pn/
| /4 width=5 by lexs_next, sle_inv_nn/
| elim (sle_inv_xp … H12) -H12 [2,3: // ]
  #g1 #H #H1 destruct /3 width=5 by lexs_push/
]
qed-.

lemma sle_lexs_conf: ∀RN,RP. (∀L,I1,I2. RP L I1 I2 → RN L I1 I2) →
                     ∀f1,L1,L2. L1 ⪤*[RN, RP, f1] L2 →
                     ∀f2. f1 ⊆ f2 → L1 ⪤*[RN, RP, f2] L2.
#RN #RP #HR #f1 #L1 #L2 #H elim H -f1 -L1 -L2 //
#f1 #I1 #I2 #L1 #L2 #_ #HI12 #IH #f2 #H12
[2: elim (pn_split f2) * ]
[ /4 width=5 by lexs_push, sle_inv_pp/
| /4 width=5 by lexs_next, sle_inv_pn/
| elim (sle_inv_nx … H12) -H12 [2,3: // ]
  #g2 #H #H2 destruct /3 width=5 by lexs_next/
]
qed-.

lemma lexs_sle_split: ∀R1,R2,RP. (∀L. reflexive … (R1 L)) → (∀L. reflexive … (R2 L)) →
                      ∀f,L1,L2. L1 ⪤*[R1, RP, f] L2 → ∀g. f ⊆ g →
                      ∃∃L. L1 ⪤*[R1, RP, g] L & L ⪤*[R2, cfull, f] L2.
#R1 #R2 #RP #HR1 #HR2 #f #L1 #L2 #H elim H -f -L1 -L2
[ /2 width=3 by lexs_atom, ex2_intro/ ]
#f #I1 #I2 #L1 #L2 #_ #HI12 #IH #y #H
[ elim (sle_inv_nx … H ??) -H [ |*: // ] #g #Hfg #H destruct
  elim (IH … Hfg) -IH -Hfg /3 width=5 by lexs_next, ex2_intro/
| elim (sle_inv_px … H ??) -H [1,3: * |*: // ] #g #Hfg #H destruct
  elim (IH … Hfg) -IH -Hfg /3 width=5 by lexs_next, lexs_push, ex2_intro/
]
qed-.

lemma lexs_dec: ∀RN,RP.
                (∀L,I1,I2. Decidable (RN L I1 I2)) →
                (∀L,I1,I2. Decidable (RP L I1 I2)) →
                ∀L1,L2,f. Decidable (L1 ⪤*[RN, RP, f] L2).
#RN #RP #HRN #HRP #L1 elim L1 -L1 [ * | #L1 #I1 #IH * ]
[ /2 width=1 by lexs_atom, or_introl/
| #L2 #I2 #f @or_intror #H
  lapply (lexs_inv_atom1 … H) -H #H destruct
| #f @or_intror #H
  lapply (lexs_inv_atom2 … H) -H #H destruct
| #L2 #I2 #f elim (IH L2 (⫱f)) -IH #HL12
  [2: /4 width=3 by lexs_fwd_bind, or_intror/ ]
  elim (pn_split f) * #g #H destruct
  [ elim (HRP L1 I1 I2) | elim (HRN L1 I1 I2) ] -HRP -HRN #HV12
  [1,3: /3 width=1 by lexs_push, lexs_next, or_introl/ ]
  @or_intror #H
  [ elim (lexs_inv_push … H) | elim (lexs_inv_next … H) ] -H
  /2 width=1 by/
]
qed-.
