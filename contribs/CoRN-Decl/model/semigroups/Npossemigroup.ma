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

set "baseuri" "cic:/matita/CoRN-Decl/model/semigroups/Npossemigroup".

include "CoRN.ma".

(* $Id: Npossemigroup.v,v 1.6 2004/04/08 08:20:34 lcf Exp $ *)

include "algebra/CSemiGroups.ma".

include "model/semigroups/Nsemigroup.ma".

include "model/setoids/Npossetoid.ma".

(*#* **Examples of semi-groups:  $\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;# and $\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
***$\langle$#&lang;#[Npos],[[+]]$\rangle$#&rang;#
The positive natural numbers form together with addition a subsemigroup 
 of the semigroup of the natural numbers with addition.
*)

inline "cic:/CoRN/model/semigroups/Npossemigroup/Npos_as_CSemiGroup.con".

(*#* ***$\langle$#&lang;#[Npos],[[*]]$\rangle$#&rang;#
Also together with multiplication, the positive numbers form a semigroup.
*)

inline "cic:/CoRN/model/semigroups/Npossemigroup/Nposmult_is_CSemiGroup.con".

inline "cic:/CoRN/model/semigroups/Npossemigroup/Nposmult_as_CSemiGroup.con".

