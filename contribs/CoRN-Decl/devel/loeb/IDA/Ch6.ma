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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/CoRN-Decl/devel/loeb/IDA/Ch6".

include "CoRN.ma".

include "algebra/CSemiGroups.ma".

(* Remark blz 65 1 *)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_nullary_operation.con".

include "model/setoids/Zsetoid.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_nullary_operation_Z_0.con".

(* Remark blz 65 2 *)

include "devel/loeb/per/csetfun.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/n_ary_operation.con".

include "model/setoids/Nsetoid.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/plus1.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_plus1_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/plus2.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_plus2_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/plus3.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/on.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ex_3_ary.con" "__".

(* blz 65 Example 1 *)

(* Print Zopp_is_fun.*)

(* Print Inv_as_un_op.
Geen goed voorbeeld: monoids komen hier al in voor en het is een heel onoverzichtelijk bewijs *)

(* blz 65 Example 2 *)

(* Print plus_is_bin_fun.*)

(* Print mult_as_bin_fun.*)

(* blz 66 Example 1 *)

(* Print plus_is_assoc.*)

(* Print Zplus_is_assoc.*)

(* Print Zmult_is_assoc.*)

include "model/setoids/Qsetoid.ma".

(* Print Qplus_is_assoc.*)

(* Print Qmult_is_assoc.*)

(* blz 66 Examples 2 *)

(* UNEXPORTED
Section p66E2
*)

alias id "X" = "cic:/CoRN/devel/loeb/IDA/Ch6/p66E2/X.var".

alias id "f" = "cic:/CoRN/devel/loeb/IDA/Ch6/p66E2/f.var".

alias id "g" = "cic:/CoRN/devel/loeb/IDA/Ch6/p66E2/g.var".

alias id "h" = "cic:/CoRN/devel/loeb/IDA/Ch6/p66E2/h.var".

(* Check comp_as_bin_op.*)

(* Check assoc_comp.*)

(* UNEXPORTED
End p66E2
*)

(* blz 66 Example 2eblok 1 *)

include "model/semigroups/Zsemigroup.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Zplus_is_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Zmult_is_CSemiGroup.con".

(* blz 66 Example % 3 *)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/FS_is_CSemiGroup.con".

(* blz 66 Example % 4 *)

(* UNEXPORTED
Section p66E2b4
*)

alias id "A" = "cic:/CoRN/devel/loeb/IDA/Ch6/p66E2b4/A.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Astar.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/empty_word.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/app.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/eq_fm.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ap_fm.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ap_fm_irreflexive.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ap_fm_symmetric.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ap_fm_cotransitive.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ap_fm_tight.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/free_csetoid_is_CSetoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/free_csetoid_as_csetoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/app_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/app_as_csb_fun.con".

include "algebra/CSemiGroups.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/eq_fm_reflexive.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Astar_is_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Astar_as_CSemiGroup.con".

(* UNEXPORTED
End p66E2b4
*)

(* Definition 5 *)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_unit.con".

(* blz 67 Remark 1 *)

include "model/monoids/Zmonoid.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_unit_Z_0.con".

(* blz 67 Remark 2 *)

(* UNEXPORTED
Section p67R2
*)

alias id "X" = "cic:/CoRN/devel/loeb/IDA/Ch6/p67R2/X.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_unit_FS_id.con".

(* UNEXPORTED
End p67R2
*)

(* blz 67 Remark 3 *)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_unit_Astar_empty_word.con".

(* Lemma 6 *)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/unique_unit.con".

(* blz 67 Example 1 *)

include "model/monoids/Nmonoid.ma".

(* Print nat_is_CMonoid.*)

include "model/monoids/Zmonoid.ma".

(* Print Z_is_CMonoid.*)

(* Print Z_mul_is_CMonoid.*)

(* blz 67 Example 3 *)

(* Print FS_is_CMonoid.*)

(* blz 68 Example blok1 1 *)

(* UNEXPORTED
Section p68E1b1
*)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1.ind".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_eq.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_ap.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_ap_irreflexive.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_ap_symmetric.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_ap_cotransitive.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_eq_dec.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/is_e1.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/not_M1_eq_e1_u.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_ap_tight.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_is_CSetoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_as_CSetoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_mult.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_CS_mult.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_CS_mult_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_mult_as_bin_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_is_CSemiGroup.con".

include "algebra/CMonoids.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1_is_lft_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1_is_rht_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_as_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_is_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_as_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_mult.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_CS_mult.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_CS_mult_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_mult_as_bin_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_is_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_as_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1_is_lft_unit_M2.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1_is_rht_unit_M2.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_is_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M2_as_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/two_element_CMonoids.con".

(* UNEXPORTED
End p68E1b1
*)

(* blz 68 Example blok2 1 *)

(* Print Zplus_is_commut.*)

(* Print Zmult_is_commut. *)

(* Print Qplus_is_commut1. *)

(* Print Qmult_is_commut. *)

(* Definition 9 *)

include "algebra/CMonoids.ma".

(* UNEXPORTED
Section D9S
*)

alias id "M1" = "cic:/CoRN/devel/loeb/IDA/Ch6/D9S/M1.var".

alias id "M2" = "cic:/CoRN/devel/loeb/IDA/Ch6/D9S/M2.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/dprod.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/dprod_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/dprod_as_csb_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/direct_product_is_CSemiGroup.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/direct_product_as_CSemiGroup.con".

(* UNEXPORTED
End D9S
*)

(* UNEXPORTED
Section D9M
*)

alias id "M1" = "cic:/CoRN/devel/loeb/IDA/Ch6/D9M/M1.var".

alias id "M2" = "cic:/CoRN/devel/loeb/IDA/Ch6/D9M/M2.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1e2_is_rht_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/e1e2_is_lft_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/direct_product_is_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/direct_product_as_CMonoid.con".

(* UNEXPORTED
End D9M
*)

(* blz 69 Example *)

(* UNEXPORTED
Section p69E1
*)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p69E1/PM1M2.con" "p69E1__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p69E1/uu.con" "p69E1__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p69E1/e1u.con" "p69E1__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ex_69.con".

(* UNEXPORTED
End p69E1
*)

(* Theorem 11 *)

(* UNEXPORTED
Section Th11
*)

alias id "M" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th11/M.var".

alias id "I" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th11/I.var".

alias id "C" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th11/C.var".

alias id "Cunit" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th11/Cunit.var".

alias id "op_pres_C" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th11/op_pres_C.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/K.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/op_pres_K.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/K_is_Monoid.con".

(* UNEXPORTED
End Th11
*)

(* Theorem 12 *)

(* UNEXPORTED
Section Th12
*)

alias id "A" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th12/A.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/nil_is_rht_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/nil_is_lft_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/free_monoid_is_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/free_monoid_as_CMonoid.con".

(* UNEXPORTED
End Th12
*)

(* blz 70 text *)

(* UNEXPORTED
Section p70text
*)

include "devel/loeb/per/lst2fun.ma".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p70text/A.con" "p70text__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/ZerolessOne.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_word.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_word'.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_word'_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_word_as_CSetoid_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/to_word_bijective.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/pres_plus_to_word.con".

(* UNEXPORTED
End p70text
*)

(* Definition 13 *)

(* UNEXPORTED
Section Th13
*)

alias id "M1" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th13/M1.var".

alias id "M2" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th13/M2.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/morphism.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/isomorphism.con".

(* UNEXPORTED
End Th13
*)

(* blz 71 Example 1 *)

(* UNEXPORTED
Section p71E1
*)

alias id "M" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E1/M.var".

alias id "c" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E1/c.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/power_CMonoid.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/power_CMonoid_CSetoid.con".

alias id "is_generated_by" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E1/is_generated_by.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p71E1/f.con" "p71E1__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/f_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/f_as_CSetoid_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/surjective_f.con".

(* UNEXPORTED
End p71E1
*)

(* UNEXPORTED
Section p71E1'
*)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/M1_is_generated_by_u.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/not_injective_f.con".

(* UNEXPORTED
End p71E1'
*)

(* Print to_word_bijective.*)

(* UNEXPORTED
Section p71E2
*)

alias id "A" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E2/A.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p71E2/L.con" "p71E2__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/L_strext.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/L_as_CSetoid_fun.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/L_is_morphism.con".

(* UNEXPORTED
End p71E2
*)

(* blz 71 Remark 1 *)

(* UNEXPORTED
Section p71R1
*)

alias id "S1" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71R1/S1.var".

alias id "S2" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71R1/S2.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/morphism_of_CSemiGroups.con".

(* UNEXPORTED
End p71R1
*)

(* UNEXPORTED
Section p71R2
*)

alias id "M" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71R2/M.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/automorphism.con".

(* UNEXPORTED
End p71R2
*)

(* Theorem 14 *)

(* UNEXPORTED
Section Th14
*)

alias id "M1" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th14/M1.var".

alias id "M2" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th14/M2.var".

alias id "f" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th14/f.var".

alias id "isof" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th14/isof.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/iso_imp_bij.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/iso_inv.con".

(* UNEXPORTED
End Th14
*)

(* blz 71 Examples 2eblok 1 *)

(* UNEXPORTED
Section p71E2b1
*)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/isomorphic.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/not_isomorphic_M1_M2.con".

(* UNEXPORTED
End p71E2b1
*)

(* UNEXPORTED
Section p71E2b2
*)

alias id "M1" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E2b2/M1.var".

alias id "M2" = "cic:/CoRN/devel/loeb/IDA/Ch6/p71E2b2/M2.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/p71E2b2/f.con" "p71E2b2__".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/f_strext'.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/f_as_CSetoid_fun'.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/isomorphic_PM1M2_PM2M1.con".

(* UNEXPORTED
End p71E2b2
*)

(* UNEXPORTED
Section Th15
*)

alias id "M" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th15/M.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/cm_Sum.con".

alias id "D" = "cic:/CoRN/devel/loeb/IDA/Ch6/Th15/D.var".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/member.con".

(* UNEXPORTED
Implicit Arguments member [A].
*)

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Dbrack.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Dbrack_unit.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/member_app.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/cm_Sum_app.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/op_pres_Dbrack.con".

inline "cic:/CoRN/devel/loeb/IDA/Ch6/Dbrack_as_CMonoid.con".

(* UNEXPORTED
End Th15
*)

