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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/Qmonoid".

include "CoRN.ma".

(* $Id: Qmonoid.v,v 1.7 2004/04/08 08:20:33 lcf Exp $ *)

include "model/semigroups/Qsemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Examples of a monoid: $\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Q],[[+]]$\rangle$#&rang;#
The rational numbers form with addition a CMonoid. [QZERO] is the unit.
*)

inline "cic:/CoRN/model/monoids/Qmonoid/ZEROQ_as_rht_unit3.con".

inline "cic:/CoRN/model/monoids/Qmonoid/ZEROQ_as_lft_unit3.con".

inline "cic:/CoRN/model/monoids/Qmonoid/Q_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Qmonoid/Q_as_CMonoid.con".

(*#* ***$\langle$#&lang;#[Q],[[*]]$\rangle$#&rang;#
Also with multiplication Q forms a CMonoid. Here, the unit is [QONE].
*)

inline "cic:/CoRN/model/monoids/Qmonoid/ONEQ_as_rht_unit.con".

inline "cic:/CoRN/model/monoids/Qmonoid/ONEQ_as_lft_unit.con".

inline "cic:/CoRN/model/monoids/Qmonoid/Q_mul_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Qmonoid/Q_mul_as_CMonoid.con".

