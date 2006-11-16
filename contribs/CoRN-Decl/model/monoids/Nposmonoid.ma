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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/Nposmonoid".

include "CoRN.ma".

(* $Id: Nposmonoid.v,v 1.6 2004/04/08 08:20:33 lcf Exp $ *)

include "model/semigroups/Npossemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Example of a monoid: $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
One is the right unit as well as the left unit of the multiplication on the
positive natural numbers.
*)

inline "cic:/CoRN/model/monoids/Nposmonoid/rhtunitNpos.con".

inline "cic:/CoRN/model/monoids/Nposmonoid/lftunitNpos.con".

(*#* So, the positive natural numbers with multiplication form a CMonoid.
*)

inline "cic:/CoRN/model/monoids/Nposmonoid/Nposmult_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Nposmonoid/Nposmult_as_CMonoid.con".

