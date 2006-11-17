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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/Qposmonoid".

include "CoRN.ma".

(* $Id: Qposmonoid.v,v 1.7 2004/04/08 08:20:33 lcf Exp $ *)

include "model/semigroups/Qpossemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Example of a monoid: $\langle$#&lang;#[Qpos],[[*]]$\rangle$#&rang;#
One is the unit for multiplication on positive integers. Therefore the positive rational numbers together with the multiplication are a CMonoid.
*)

inline "cic:/CoRN/model/monoids/Qposmonoid/QONEpos_is_rht_unit.con".

inline "cic:/CoRN/model/monoids/Qposmonoid/QONEpos_is_lft_unit.con".

inline "cic:/CoRN/model/monoids/Qposmonoid/Qpos_mult_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Qposmonoid/Qpos_mult_as_CMonoid.con".

