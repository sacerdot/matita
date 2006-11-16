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

set "baseuri" "cic:/matita/CoRN-Decl/model/non_examples/Npos_no_monoid".

include "CoRN.ma".

(* $Id: Npos_no_monoid.v,v 1.5 2004/04/08 08:20:34 lcf Exp $ *)

include "model/semigroups/Npossemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Non-example of a monoid: $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
There is no right unit for the addition on the positive natural numbers.
*)

inline "cic:/CoRN/model/non_examples/Npos_no_monoid/no_rht_unit_Npos.con".

(*#* Therefore the set of positive natural numbers doesn't form a group with 
addition.
*)

inline "cic:/CoRN/model/non_examples/Npos_no_monoid/no_monoid_Npos.con".

