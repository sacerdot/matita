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

include "basic_2/static/lfeq.ma".
include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/i_static/tc_lfxs_fqup.ma".

(*
axiom cext2_inv_LTC: ∀R,L,I1,I2. cext2 (LTC … R) L I1 I2 → LTC … (cext2 R) L I1 I2.

#R #L #I1 #I2 * -I1 -I2
[ /2 width=1 by ext2_unit, inj/
| #I #V1 #V2 #HV12 
*)

  
(*
lemma pippo: ∀RN,RP. (∀L. reflexive … (RP L)) →
             ∀f,L1,L2. L1 ⪤*[LTC … RN, RP, f] L2 →
             TC … (lexs RN RP f) L1 L2.
#RN #RP #HRP #f #L1 #L2 #H elim H -f -L1 -L2
[ /2 width=1 by lexs_atom, inj/ ]
#f #I1 #I2 #L1 #L2 #HL12 #HI12 #IH 
[ @step [3: 
*)

(*
axiom lexs_frees_confluent_LTC_sn: ∀RN,RP. lexs_frees_confluent RN RP →
                                   lexs_frees_confluent (LTC … RN) RP.

#RN #RP #HR #f1 #L1 #T #Hf1 #L2 #H  
*)
(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

lemma pippo: ∀R. (∀L. reflexive … (R L)) →
             (lexs_frees_confluent (cext2 R) cfull) →
             ∀L1,L2,T. L1 ⪤**[R, T] L2 →
             ∃∃L. L1 ⪤*[LTC … R, T] L & L ≡[T] L2.
#R #H1R #H2R #L1 #L2 #T #H
@(tc_lfxs_ind_sn … H1R … H) -H -L2
[ /4 width=5 by lfxs_refl, inj, ex2_intro/
| #L0 #L2 #_ #HL02 * #L * #f1 #Hf1 #HL1 #HL0
  lapply (lexs_co ??? cfull … (cext2_inv_LTC R) … HL1) -HL1 // #HL1
  lapply (lfeq_lfxs_trans … HL0 … HL02) -L0 #HL2
  elim (lexs_frees_confluent_LTC_sn … H2R … Hf1 … HL1) #f2 #Hf2 #Hf21
  lapply (lfxs_inv_frees … HL2 … Hf2) -HL2 #HL2
  elim (lexs_sle_split … ceq_ext … HL2 … Hf21) -HL2
  [ #L0 #HL0 #HL02
  |*: /2 width=1 by ext2_refl/
  ]
  lapply (sle_lexs_trans … HL0 … Hf21) -Hf21 // #H
  elim (H2R … Hf2 … H) -H #f0 #Hf0 #Hf02
  lapply (sle_lexs_trans … HL02 … Hf02) -f2 // #HL02
  @(ex2_intro … L0)
  [ @(ex2_intro … Hf1)
  | @(ex2_intro … HL02) //
