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

set "baseuri" "cic:/matita/CoRN-Decl/model/non_examples/Npos_no_group".

include "CoRN.ma".

(* $Id: Npos_no_group.v,v 1.6 2004/04/08 08:20:33 lcf Exp $ *)

include "algebra/CGroups.ma".

include "model/monoids/Nposmonoid.ma".

(*#* **Non-example of a group: $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
There is no inverse for multiplication on the positive natural numbers.
*)

inline "cic:/CoRN/model/non_examples/Npos_no_group/no_inverse_Nposmult.con".

(*#* Hence the natural numbers with multiplication do not form a group.
*)

inline "cic:/CoRN/model/non_examples/Npos_no_group/no_group_Nposmult.con".

