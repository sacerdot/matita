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

set "baseuri" "cic:/matita/CoRN-Decl/model/setoids/Qsetoid".

include "CoRN.ma".

(* $Id: Qsetoid.v,v 1.6 2004/04/06 15:46:05 lcf Exp $ *)

include "model/structures/Qsec.ma".

include "algebra/CSetoidFun.ma".

(*#* **Example of a setoid: [Q]
***Setoid
*)

inline "cic:/CoRN/model/setoids/Qsetoid/ap_Q_irreflexive1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/ap_Q_symmetric1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/ap_Q_cotransitive1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/ap_Q_tight1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/ap_Q_is_apartness.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Q_as_CSetoid.con".

(*#* ***Addition
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qplus_wd.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qplus_strext1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qplus_is_bin_fun.con".

(*#* It is associative and commutative.
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qplus_is_assoc.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qplus_is_commut1.con".

(*#* ***Opposite
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qopp_wd.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qopp_strext.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qopp_is_fun.con".

(*#* ***Multiplication
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qmult_wd.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qmult_strext1.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qmult_is_bin_fun.con".

(*#* It is associative and commutative.
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qmult_is_assoc.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qmult_is_commut.con".

(*#* ***Less-than
*)

inline "cic:/CoRN/model/setoids/Qsetoid/Qlt_strext.con".

inline "cic:/CoRN/model/setoids/Qsetoid/Qlt_is_CSetoid_relation.con".

