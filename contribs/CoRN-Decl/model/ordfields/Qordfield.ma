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

set "baseuri" "cic:/matita/CoRN-Decl/model/ordfields/Qordfield".

include "CoRN.ma".

(* $Id: Qordfield.v,v 1.9 2004/04/23 10:01:03 lcf Exp $ *)

include "model/fields/Qfield.ma".

include "algebra/COrdFields.ma".

(*#* **Example of an ordered field: $\langle$#&lang;#[Q],[[+]],[[*]],[[<]]$\rangle$#&rang;#
 [Q] is an archemaedian ordered field.
*)

inline "cic:/CoRN/model/ordfields/Qordfield/Qlt_is_strict_order.con".

inline "cic:/CoRN/model/ordfields/Qordfield/Q_is_COrdField.con".

inline "cic:/CoRN/model/ordfields/Qordfield/Q_as_COrdField.con".

inline "cic:/CoRN/model/ordfields/Qordfield/Q_is_archemaedian.con".

