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

set "baseuri" "cic:/matita/CoRN-Decl/model/non_examples/N_no_group".

include "CoRN.ma".

(* $Id: N_no_group.v,v 1.5 2004/04/08 08:20:33 lcf Exp $ *)

include "model/monoids/Nmonoid.ma".

include "algebra/CGroups.ma".

(*#* **Non-example of a group: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
There is no inverse function for the natural numbers with addition.
*)

inline "cic:/CoRN/model/non_examples/N_no_group/no_inverse_nat_plus.con".

(*#* Hence they do not form a CGroup.
*)

inline "cic:/CoRN/model/non_examples/N_no_group/no_group_nat_plus.con".

