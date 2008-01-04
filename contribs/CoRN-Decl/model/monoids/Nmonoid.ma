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

set "baseuri" "cic:/matita/CoRN-Decl/model/monoids/Nmonoid".

include "CoRN.ma".

(* $Id: Nmonoid.v,v 1.5 2004/04/08 08:20:32 lcf Exp $ *)

include "model/semigroups/Nsemigroup.ma".

include "algebra/CMonoids.ma".

(*#* **Example of a monoid: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
Zero is an unit for the addition.
*)

inline "cic:/CoRN/model/monoids/Nmonoid/O_as_rht_unit.con".

inline "cic:/CoRN/model/monoids/Nmonoid/O_as_lft_unit.con".

inline "cic:/CoRN/model/monoids/Nmonoid/nat_is_CMonoid.con".

(*#*
 Whence we can define #<i>#%\emph{%the monoid of natural numbers%}%#</i>#:
*)

inline "cic:/CoRN/model/monoids/Nmonoid/nat_as_CMonoid.con".

