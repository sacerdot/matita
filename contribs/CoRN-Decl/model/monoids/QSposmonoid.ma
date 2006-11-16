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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/QSposmonoid".

include "CoRN.ma".

(* $Id: QSposmonoid.v,v 1.5 2004/04/08 08:20:33 lcf Exp $ *)

include "model/semigroups/QSpossemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Example of a monoid: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
Two is the unit of the operation  $(x,y) \mapsto xy/2$ #(x,y) 
  &#x21A6; xy/2# on the positive rationals. So we have another monoid structure on the positive rational numbers.
*)

inline "cic:/CoRN/model/monoids/QSposmonoid/QTWOpos_is_rht_unit.con".

inline "cic:/CoRN/model/monoids/QSposmonoid/QTWOpos_is_lft_unit.con".

inline "cic:/CoRN/model/monoids/QSposmonoid/Qpos_multdiv2_is_CMonoid.con".

inline "cic:/CoRN/model/monoids/QSposmonoid/Qpos_multdiv2_as_CMonoid.con".

