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

include "basic_2/relocation/lpx_sn.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

definition lpx_sn_confluent: relation (relation3 lenv term term) ≝ λR1,R2.
                             ∀L0,T0,T1. R1 L0 T0 T1 → ∀T2. R2 L0 T0 T2 →
                             ∀L1. lpx_sn (λ_.R1) L0 L1 → ∀L2. lpx_sn (λ_.R2) L0 L2 →
                             ∃∃T. R2 L1 T1 T & R1 L2 T2 T.

definition lpx_sn_transitive: relation (relation3 lenv term term) ≝ λR1,R2.
                              ∀L1,T1,T. R1 L1 T1 T → ∀L2. lpx_sn (λ_.R1) L1 L2 →
                              ∀T2. R2 L2 T T2 → R1 L1 T1 T2.

(* Main properties **********************************************************)

theorem lpx_sn_trans: ∀R. lpx_sn_transitive R R → Transitive … (lpx_sn (λ_.R)).
#R #HR #L1 #L #H elim H -L1 -L //
#I #L1 #L #V1 #V #HL1 #HV1 #IHL1 #X #H
elim (lpx_sn_inv_pair1 … H) -H #L2 #V2 #HL2 #HV2 #H destruct /3 width=5 by lpx_sn_pair/
qed-.

theorem lpx_sn_conf: ∀R1,R2. lpx_sn_confluent R1 R2 →
                     confluent2 … (lpx_sn (λ_.R1)) (lpx_sn (λ_.R2)).
#R1 #R2 #HR12 #L0 @(f_ind … length … L0) -L0 #n #IH *
[ #_ #X1 #H1 #X2 #H2 -n
  >(lpx_sn_inv_atom1 … H1) -X1
  >(lpx_sn_inv_atom1 … H2) -X2 /2 width=3 by lpx_sn_atom, ex2_intro/
| #L0 #I #V0 #Hn #X1 #H1 #X2 #H2 destruct
  elim (lpx_sn_inv_pair1 … H1) -H1 #L1 #V1 #HL01 #HV01 #H destruct
  elim (lpx_sn_inv_pair1 … H2) -H2 #L2 #V2 #HL02 #HV02 #H destruct
  elim (IH … HL01 … HL02) -IH normalize // #L #HL1 #HL2
  elim (HR12 … HV01 … HV02 … HL01 … HL02) -L0 -V0 /3 width=5 by lpx_sn_pair, ex2_intro/
]
qed-.
