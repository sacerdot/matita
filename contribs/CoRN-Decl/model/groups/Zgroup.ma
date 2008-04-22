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

set "baseuri" "cic:/matita/CoRN-Decl/model/groups/Zgroup".

include "CoRN.ma".

(* $Id: Zgroup.v,v 1.5 2004/04/08 08:20:32 lcf Exp $ *)

include "model/monoids/Zmonoid.ma".

include "algebra/CGroups.ma".

(*#* **Example of a group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

inline "cic:/CoRN/model/groups/Zgroup/Z_is_CGroup.con".

inline "cic:/CoRN/model/groups/Zgroup/Z_as_CGroup.con".

(*#* The term [Z_as_CGroup] is of type [CGroup]. Hence we have proven that [Z] is a constructive group. *)

