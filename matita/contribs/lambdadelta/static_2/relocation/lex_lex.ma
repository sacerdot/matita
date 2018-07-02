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

include "static_2/relocation/lex.ma".

(* GENERIC ENTRYWISE EXTENSION OF CONTEXT-SENSITIVE REALTIONS FOR TERMS *****)

(* Main properties **********************************************************)

(* Basic_2A1: was: lpx_sn_trans *)
theorem lex_trans (R): lex_transitive R R → Transitive … (lex R).
#R #HR #L1 #L #H @(lex_ind … H) -L1 -L //
[ #I #K1 #K #HK1 #IH #Y #H
  elim (lex_inv_unit_sn … H) -H #K2 #K2 #H destruct
  /3 width=1 by lex_unit/
| #I #K1 #L #V1 #V #HK1 #IH #HV1 #X #H
  elim (lex_inv_pair_sn … H) -H #K2 #V2 #HK2 #HV2 #H destruct
  /3 width=5 by lex_pair/
]
qed-.

(* Basic_2A1: was: lpx_sn_conf *)
theorem lex_conf (R1) (R2): lex_confluent R1 R2 → confluent2 … (lex R1) (lex R2).
#R1 #R2 #HR12 #L0 elim L0 -L0 [| #K0 * ]
[ #Y1 #H1 #Y2 #H2
  >(lex_inv_atom_sn … H1) -Y1
  >(lex_inv_atom_sn … H2) -Y2
  /2 width=3 by lex_atom, ex2_intro/
| #I #IH #Y1 #H1 #Y2 #H2
  elim (lex_inv_unit_sn … H1) -H1 #K1 #HK01 #H destruct
  elim (lex_inv_unit_sn … H2) -H2 #K2 #HK02 #H destruct
  elim (IH … HK01 … HK02) -K0 #K #HK1 #HK2
  /3 width=3 by lex_unit, ex2_intro/
| #I #V0 #IH #Y1 #H1 #Y2 #H2
  elim (lex_inv_pair_sn … H1) -H1 #K1 #V1 #HK01 #HV01 #H destruct
  elim (lex_inv_pair_sn … H2) -H2 #K2 #V2 #HK02 #HV02 #H destruct
  elim (HR12 … HV01 … HV02 … HK01 … HK02) -V0 #V #HV1 #HV2
  elim (IH … HK01 … HK02) -K0 #K #HK1 #HK2
  /3 width=5 by lex_pair, ex2_intro/
]
qed-.
