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

set "baseuri" "cic:/matita/CoRN-Decl/model/semigroups/Zsemigroup".

include "CoRN.ma".

(* $Id: Zsemigroup.v,v 1.6 2004/04/08 08:20:35 lcf Exp $ *)

include "model/setoids/Zsetoid.ma".

include "algebra/CSemiGroups.ma".

(*#* **Examples of semi-groups: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

inline "cic:/CoRN/model/semigroups/Zsemigroup/Z_as_CSemiGroup.con".

(*#* The term [Z_as_CSemiGroup] is of type [CSemiGroup]. Hence we have proven that [Z] is a constructive semi-group. *)

(*#* ***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
*)

inline "cic:/CoRN/model/semigroups/Zsemigroup/Z_mul_as_CSemiGroup.con".

