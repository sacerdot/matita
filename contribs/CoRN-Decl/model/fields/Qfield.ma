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

set "baseuri" "cic:/matita/CoRN-Decl/model/fields/Qfield".

include "CoRN.ma".

(* $Id: Qfield.v,v 1.8 2004/04/08 08:20:32 lcf Exp $ *)

include "model/rings/Qring.ma".

include "algebra/CFields.ma".

(*#* **Example of a field: $\langle$#&lang;#[Q],[[+]],[[*]]$\rangle$#&rang;#
As we have seen, there is a inverse for the multiplication for non-zeroes.
So, [Q] not only forms a ring, but even a field.
*)

inline "cic:/CoRN/model/fields/Qfield/Q_is_CField.con".

inline "cic:/CoRN/model/fields/Qfield/Q_as_CField.con".

