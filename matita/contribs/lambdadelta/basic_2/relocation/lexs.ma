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

include "ground_2/relocation/nstream_sle.ma".
include "basic_2/notation/relations/relationstar_5.ma".
include "basic_2/grammar/lenv.ma".

(* GENERAL ENTRYWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Basic_2A1: includes: lpx_sn_atom lpx_sn_pair *)
inductive lexs (RN,RP:relation3 lenv term term): rtmap → relation lenv ≝
| lexs_atom: ∀f. lexs RN RP f (⋆) (⋆)
| lexs_next: ∀I,L1,L2,V1,V2,f.
             lexs RN RP f L1 L2 → RN L1 V1 V2 →
             lexs RN RP (⫯f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
| lexs_push: ∀I,L1,L2,V1,V2,f.
             lexs RN RP f L1 L2 → RP L1 V1 V2 →
             lexs RN RP (↑f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation "general entrywise extension (local environment)"
   'RelationStar RN RP f L1 L2 = (lexs RN RP f L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lexs_inv_atom1_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → X = ⋆ → Y = ⋆.
#RN #RP #X #Y #f * -X -Y -f //
#I #L1 #L2 #V1 #V2 #f #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom1 *)
lemma lexs_inv_atom1: ∀RN,RP,Y,f. ⋆ ⦻*[RN, RP, f] Y → Y = ⋆.
/2 width=6 by lexs_inv_atom1_aux/ qed-.

fact lexs_inv_next1_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → ∀J,K1,W1,g. X = K1.ⓑ{J}W1 → f = ⫯g →
                         ∃∃K2,W2. K1 ⦻*[RN, RP, g] K2 & RN K1 W1 W2 & Y = K2.ⓑ{J}W2.
#RN #RP #X #Y #f * -X -Y -f
[ #f #J #K1 #W1 #g #H destruct
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K1 #W1 #g #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #I #L1 #L2 #V1 #V2 #f #_ #_ #J #K1 #W1 #g #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair1 *)
lemma lexs_inv_next1: ∀RN,RP,J,K1,Y,W1,g. K1.ⓑ{J}W1 ⦻*[RN, RP, ⫯g] Y →
                      ∃∃K2,W2. K1 ⦻*[RN, RP, g] K2 & RN K1 W1 W2 & Y = K2.ⓑ{J}W2.
/2 width=7 by lexs_inv_next1_aux/ qed-.


fact lexs_inv_push1_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → ∀J,K1,W1,g. X = K1.ⓑ{J}W1 → f = ↑g →
                         ∃∃K2,W2. K1 ⦻*[RN, RP, g] K2 & RP K1 W1 W2 & Y = K2.ⓑ{J}W2.
#RN #RP #X #Y #f * -X -Y -f
[ #f #J #K1 #W1 #g #H destruct
| #I #L1 #L2 #V1 #V2 #f #_ #_ #J #K1 #W1 #g #_ #H elim (discr_next_push … H)
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K1 #W1 #g #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push1: ∀RN,RP,J,K1,Y,W1,g. K1.ⓑ{J}W1 ⦻*[RN, RP, ↑g] Y →
                      ∃∃K2,W2. K1 ⦻*[RN, RP, g] K2 & RP K1 W1 W2 & Y = K2.ⓑ{J}W2.
/2 width=7 by lexs_inv_push1_aux/ qed-.

fact lexs_inv_atom2_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → Y = ⋆ → X = ⋆.
#RN #RP #X #Y #f * -X -Y -f //
#I #L1 #L2 #V1 #V2 #f #_ #_ #H destruct
qed-.

(* Basic_2A1: includes lpx_sn_inv_atom2 *)
lemma lexs_inv_atom2: ∀RN,RP,X,f. X ⦻*[RN, RP, f] ⋆ → X = ⋆.
/2 width=6 by lexs_inv_atom2_aux/ qed-.

fact lexs_inv_next2_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → ∀J,K2,W2,g. Y = K2.ⓑ{J}W2 → f = ⫯g →
                         ∃∃K1,W1. K1 ⦻*[RN, RP, g] K2 & RN K1 W1 W2 & X = K1.ⓑ{J}W1.
#RN #RP #X #Y #f * -X -Y -f
[ #f #J #K2 #W2 #g #H destruct
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K2 #W2 #g #H1 #H2 <(injective_next … H2) -g destruct
  /2 width=5 by ex3_2_intro/
| #I #L1 #L2 #V1 #V2 #f #_ #_ #J #K2 #W2 #g #_ #H elim (discr_push_next … H)
]
qed-.

(* Basic_2A1: includes lpx_sn_inv_pair2 *)
lemma lexs_inv_next2: ∀RN,RP,J,X,K2,W2,g. X ⦻*[RN, RP, ⫯g] K2.ⓑ{J}W2 →
                      ∃∃K1,W1. K1 ⦻*[RN, RP, g] K2 & RN K1 W1 W2 & X = K1.ⓑ{J}W1.
/2 width=7 by lexs_inv_next2_aux/ qed-.

fact lexs_inv_push2_aux: ∀RN,RP,X,Y,f. X ⦻*[RN, RP, f] Y → ∀J,K2,W2,g. Y = K2.ⓑ{J}W2 → f = ↑g →
                         ∃∃K1,W1. K1 ⦻*[RN, RP, g] K2 & RP K1 W1 W2 & X = K1.ⓑ{J}W1.
#RN #RP #X #Y #f * -X -Y -f
[ #f #J #K2 #W2 #g #H destruct
| #I #L1 #L2 #V1 #V2 #f #_ #_ #J #K2 #W2 #g #_ #H elim (discr_next_push … H)
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K2 #W2 #g #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

lemma lexs_inv_push2: ∀RN,RP,J,X,K2,W2,g. X ⦻*[RN, RP, ↑g] K2.ⓑ{J}W2 →
                      ∃∃K1,W1. K1 ⦻*[RN, RP, g] K2 & RP K1 W1 W2 & X = K1.ⓑ{J}W1.
/2 width=7 by lexs_inv_push2_aux/ qed-.

(* Basic_2A1: includes lpx_sn_inv_pair *)
lemma lexs_inv_next: ∀RN,RP,I1,I2,L1,L2,V1,V2,f.
                     L1.ⓑ{I1}V1 ⦻*[RN, RP, ⫯f] (L2.ⓑ{I2}V2) →
                     ∧∧ L1 ⦻*[RN, RP, f] L2 & RN L1 V1 V2 & I1 = I2.
#RN #RP #I1 #I2 #L1 #L2 #V1 #V2 #f #H elim (lexs_inv_next1 … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

lemma lexs_inv_push: ∀RN,RP,I1,I2,L1,L2,V1,V2,f.
                     L1.ⓑ{I1}V1 ⦻*[RN, RP, ↑f] (L2.ⓑ{I2}V2) →
                     ∧∧ L1 ⦻*[RN, RP, f] L2 & RP L1 V1 V2 & I1 = I2.
#RN #RP #I1 #I2 #L1 #L2 #V1 #V2 #f #H elim (lexs_inv_push1 … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

(* Basic properties *********************************************************)

lemma lexs_eq_repl_back: ∀RN,RP,L1,L2. eq_stream_repl_back … (λf. L1 ⦻*[RN, RP, f] L2).
#RN #RP #L1 #L2 #f1 #H elim H -L1 -L2 -f1 //
#I #L1 #L2 #V1 #v2 #f1 #_ #HV #IH #f2 #H
[ elim (next_inv_sn … H) -H /3 width=1 by lexs_next/
| elim (push_inv_sn … H) -H /3 width=1 by lexs_push/
]
qed-.

lemma lexs_eq_repl_fwd: ∀RN,RP,L1,L2. eq_stream_repl_fwd … (λf. L1 ⦻*[RN, RP, f] L2).
#RN #RP #L1 #L2 @eq_stream_repl_sym /2 width=3 by lexs_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Note: fexs_sym and fexs_trans hold, but lexs_sym and lexs_trans do not  *)
(* Basic_2A1: includes: lpx_sn_refl *)
lemma lexs_refl: ∀RN,RP,f.
                 (∀L. reflexive … (RN L)) →
                 (∀L. reflexive … (RP L)) →
                 reflexive … (lexs RN RP f).
#RN #RP #f #HRN #HRP #L generalize in match f; -f elim L -L //
#L #I #V #IH * * /2 width=1 by lexs_next, lexs_push/
qed.

lemma sle_lexs_trans: ∀RN,RP. (∀L,T1,T2. RN L T1 T2 → RP L T1 T2) →
                      ∀L1,L2,f2. L1 ⦻*[RN, RP, f2] L2 →
                      ∀f1. f1 ⊆ f2 → L1 ⦻*[RN, RP, f1] L2.
#RN #RP #HR #L1 #L2 #f2 #H elim H -L1 -L2 -f2 //
#I #L1 #L2 #V1 #V2 #f2 #_ #HV12 #IH
[ * * [2: #n1 ] ] #f1 #H
[ /4 width=5 by lexs_next, sle_inv_SS_aux/
| /4 width=5 by lexs_push, sle_inv_OS_aux/
| elim (sle_inv_xO_aux … H) -H [3: // |2: skip ]
  #g1 #H #H1 destruct /3 width=5 by lexs_push/
]
qed-.

lemma sle_lexs_conf: ∀RN,RP. (∀L,T1,T2. RP L T1 T2 → RN L T1 T2) →
                     ∀L1,L2,f1. L1 ⦻*[RN, RP, f1] L2 →
                     ∀f2. f1 ⊆ f2 → L1 ⦻*[RN, RP, f2] L2.
#RN #RP #HR #L1 #L2 #f2 #H elim H -L1 -L2 -f2 //
#I #L1 #L2 #V1 #V2 #f1 #_ #HV12 #IH
[2: * * [2: #n2 ] ] #f2 #H
[ /4 width=5 by lexs_next, sle_inv_OS_aux/
| /4 width=5 by lexs_push, sle_inv_OO_aux/
| elim (sle_inv_Sx_aux … H) -H [3: // |2: skip ]
  #g2 #H #H2 destruct /3 width=5 by lexs_next/
]
qed-.

lemma lexs_co: ∀RN1,RP1,RN2,RP2.
               (∀L1,T1,T2. RN1 L1 T1 T2 → RN2 L1 T1 T2) →
               (∀L1,T1,T2. RP1 L1 T1 T2 → RP2 L1 T1 T2) →
               ∀L1,L2,f. L1 ⦻*[RN1, RP1, f] L2 → L1 ⦻*[RN2, RP2, f] L2.
#RN1 #RP1 #RN2 #RP2 #HRN #HRP #L1 #L2 #f #H elim H -L1 -L2 -f
/3 width=1 by lexs_atom, lexs_next, lexs_push/
qed-.

(* Basic_2A1: removed theorems 17:
              llpx_sn_inv_bind llpx_sn_inv_flat
              llpx_sn_fwd_lref llpx_sn_fwd_pair_sn llpx_sn_fwd_length
              llpx_sn_fwd_bind_sn llpx_sn_fwd_bind_dx llpx_sn_fwd_flat_sn llpx_sn_fwd_flat_dx
              llpx_sn_refl llpx_sn_Y llpx_sn_bind_O llpx_sn_ge_up llpx_sn_ge llpx_sn_co
              llpx_sn_fwd_drop_sn llpx_sn_fwd_drop_dx              
*)
