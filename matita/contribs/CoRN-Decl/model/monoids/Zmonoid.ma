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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/Zmonoid".

include "CoRN.ma".

(* $Id: Zmonoid.v,v 1.6 2004/04/08 08:20:33 lcf Exp $ *)

include "model/semigroups/Zsemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Examples of monoids: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
We use the addition [ZERO] (defined in the standard library) as the
unit of monoid:
*)

inline "cic:/CoRN/model/monoids/Zmonoid/ZERO_as_rht_unit.con".

inline "cic:/CoRN/model/monoids/Zmonoid/ZERO_as_lft_unit.con".

inline "cic:/CoRN/model/monoids/Zmonoid/Z_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Zmonoid/Z_as_CMonoid.con".

(*#* The term [Z_as_CMonoid] is of type [CMonoid]. Hence we have proven that [Z] is a constructive monoid.

***$\langle$#&lang;#[Z],[[*]]$\rangle$#&rang;#
As the multiplicative unit we should use [`1`], which is [(POS xH)] in
the representation we have for integers.
*)

inline "cic:/CoRN/model/monoids/Zmonoid/ONE_as_rht_unit.con".

inline "cic:/CoRN/model/monoids/Zmonoid/ONE_as_lft_unit.con".

inline "cic:/CoRN/model/monoids/Zmonoid/Z_mul_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/Zmonoid/Z_mul_as_CMonoid.con".

(*#* The term [Z_mul_as_CMonoid] is another term of type [CMonoid]. *)

