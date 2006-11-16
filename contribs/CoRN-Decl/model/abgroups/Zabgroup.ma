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

set "baseuri" "cic:/matita/CoRN-Decl/model/abgroups/Zabgroup".

include "CoRN.ma".

(* $Id: Zabgroup.v,v 1.5 2004/04/08 08:20:32 lcf Exp $ *)

include "model/groups/Zgroup.ma".

include "algebra/CAbGroups.ma".

(*#* **Example of an abelian group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

inline "cic:/CoRN/model/abgroups/Zabgroup/Z_is_CAbGroup.con".

inline "cic:/CoRN/model/abgroups/Zabgroup/Z_as_CAbGroup.con".

(*#* The term [Z_as_CAbGroup] is of type [CAbGroup]. Hence we have proven that [Z] is a constructive Abelian group. *)

