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

set "baseuri" "cic:/matita/CoRN-Decl/devel/loeb/per/csetfun".

include "CoRN.ma".

include "algebra/CSetoids.ma".

include "algebra/CSetoidFun.ma".

inline "cic:/CoRN/devel/loeb/per/csetfun/ap_fun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/eq_fun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/irrefl_apfun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/cotrans_apfun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/ta_apfun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/sym_apfun.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_is_CSetoid.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_as_CSetoid.con".

(* UNEXPORTED
Print associative.
*)

inline "cic:/CoRN/devel/loeb/per/csetfun/comp.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/comp_as_bin_op.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/assoc_comp.con".

include "algebra/CSemiGroups.ma".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_as_CSemiGroup.con".

include "algebra/CMonoids.ma".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_id.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/id_is_rht_unit.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/id_is_lft_unit.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_is_CMonoid.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/FS_as_CMonoid.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/PS_as_CMonoid.con".

include "algebra/CGroups.ma".

inline "cic:/CoRN/devel/loeb/per/csetfun/Inv_is_bij.con".

(* Lemma Inv_is_bij :
 forall (A B : CSetoid) (f : CSetoid_fun A B) (H : bijective f),
 bijective (Inv f H).
intros A B f.
case f.
unfold fun_strext in |- *.
intros f0 H5.
unfold bijective in |- *.
intro H.
elim H.
clear H.
unfold injective in |- *.
unfold surjective in |- *.
intros H0 H1.
split.
unfold Inv in |- *.
simpl in |- *.
unfold invfun in |- *.
simpl in |- *.
unfold sigT_rect in |- *.
intros a0 a1 H2.
case H1.
case (H1 a1).
intros x H3 y H4.
simpl in H3.
simpl in H4.
simpl in H0.
simpl in H1.
apply H5.
astepl a0.
astepr a1.
exact H2.

simpl in |- *.
unfold invfun in |- *.
simpl in |- *.
unfold sigT_rect in |- *.
intros b.
exists (f0 b).
case (H1 (f0 b)).
simpl in |- *.
intros x H2.
simpl in H0.
simpl in H1.
apply not_ap_imp_eq.
red in |- *.
intro H3.
set (H4 := H0 x b H3) in *.
set (H6 := ap_imp_neq B (f0 x) (f0 b) H4) in *.
intuition.
Qed.*)

inline "cic:/CoRN/devel/loeb/per/csetfun/PS_Inv.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/Inv_as_un_op.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/PS_is_CGroup.con".

inline "cic:/CoRN/devel/loeb/per/csetfun/PS_as_CGroup.con".

(* In het algemeen niet Abels! *)

