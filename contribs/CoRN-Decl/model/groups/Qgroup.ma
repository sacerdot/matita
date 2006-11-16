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

set "baseuri" "cic:/matita/CoRN-Decl/model/groups/Qgroup".

include "CoRN.ma".

(* $Id: Qgroup.v,v 1.5 2004/04/08 08:20:32 lcf Exp $ *)

include "model/monoids/Qmonoid.ma".

include "algebra/CGroups.ma".

(*#* **Example of a group: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
The rational numbers with addition form a group. The inverse function is taking the opposite.
*)

inline "cic:/CoRN/model/groups/Qgroup/Q_is_CGroup.con".

inline "cic:/CoRN/model/groups/Qgroup/Q_as_CGroup.con".

