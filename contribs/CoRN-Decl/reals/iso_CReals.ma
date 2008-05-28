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

set "baseuri" "cic:/matita/CoRN-Decl/reals/iso_CReals".

include "CoRN.ma".

(* begin hide *)

(* in this file the  concrete canonical isomorphism -in te sense of 
   R_morphisms.v - between two arbitrary model of real numbers is built *)

include "reals/Q_dense.ma".

include "reals/R_morphism.ma".

inline "cic:/CoRN/reals/iso_CReals/less_pres_Lim.con".

inline "cic:/CoRN/reals/iso_CReals/Lim_pres_less.con".

inline "cic:/CoRN/reals/iso_CReals/inj_seq_less.con".

inline "cic:/CoRN/reals/iso_CReals/less_inj_seq.con".

inline "cic:/CoRN/reals/iso_CReals/SeqLimit_unique.con".

inline "cic:/CoRN/reals/iso_CReals/Lim_well_def.con".

inline "cic:/CoRN/reals/iso_CReals/Lim_one_one.con".

inline "cic:/CoRN/reals/iso_CReals/inj_seq_well_def.con".

inline "cic:/CoRN/reals/iso_CReals/inj_Q_one_one.con".

inline "cic:/CoRN/reals/iso_CReals/Lim_pres_plus.con".

inline "cic:/CoRN/reals/iso_CReals/G_pres_plus.con".

(* This theorem can be avoided but it is interesting *)

inline "cic:/CoRN/reals/iso_CReals/nonarchemaedian_bound_for_Lim.con".

inline "cic:/CoRN/reals/iso_CReals/Lim_pres_mult.con".

inline "cic:/CoRN/reals/iso_CReals/G_pres_mult.con".

(* UNEXPORTED
Section Concrete_iso_between_Creals
*)

alias id "R1" = "cic:/CoRN/reals/iso_CReals/Concrete_iso_between_Creals/R1.var".

alias id "R2" = "cic:/CoRN/reals/iso_CReals/Concrete_iso_between_Creals/R2.var".

inline "cic:/CoRN/reals/iso_CReals/image_Cauchy12.con".

inline "cic:/CoRN/reals/iso_CReals/image_Cauchy21.con".

inline "cic:/CoRN/reals/iso_CReals/image_G_as_CauchySeq12.con".

inline "cic:/CoRN/reals/iso_CReals/image_G_as_CauchySeq21.con".

inline "cic:/CoRN/reals/iso_CReals/f12.con".

inline "cic:/CoRN/reals/iso_CReals/g21.con".

(*#****** ISO FROM R1 TO R2 ********)

inline "cic:/CoRN/reals/iso_CReals/f12_is_inverse_g21.con".

inline "cic:/CoRN/reals/iso_CReals/f12_is_surjective.con".

inline "cic:/CoRN/reals/iso_CReals/f12_strong_ext.con".

inline "cic:/CoRN/reals/iso_CReals/f12_pres_less.con".

inline "cic:/CoRN/reals/iso_CReals/f12_pres_plus.con".

inline "cic:/CoRN/reals/iso_CReals/f12_pres_mult.con".

(*#********* ISO FROM R2 TO R1 **********)

inline "cic:/CoRN/reals/iso_CReals/g21_is_inverse_f12.con".

inline "cic:/CoRN/reals/iso_CReals/g21_is_surjective.con".

inline "cic:/CoRN/reals/iso_CReals/g21_strong_ext.con".

inline "cic:/CoRN/reals/iso_CReals/g21_pres_less.con".

inline "cic:/CoRN/reals/iso_CReals/g21_pres_plus.con".

inline "cic:/CoRN/reals/iso_CReals/g21_pres_mult.con".

(*#** Building Homomorphisms out of f12 and g21 ***)

inline "cic:/CoRN/reals/iso_CReals/f12_as_Homomorphism.con".

inline "cic:/CoRN/reals/iso_CReals/g21_as_Homomorphism.con".

inline "cic:/CoRN/reals/iso_CReals/f12_inverse_lft.con".

inline "cic:/CoRN/reals/iso_CReals/g21_inverse_rht.con".

inline "cic:/CoRN/reals/iso_CReals/Canonic_Isomorphism_between_CReals.con".

(* UNEXPORTED
End Concrete_iso_between_Creals
*)

(* end hide *)

