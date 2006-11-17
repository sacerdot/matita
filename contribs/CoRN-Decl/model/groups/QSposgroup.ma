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

set "baseuri" "cic:/matita/CoRN-Decl/model/groups/QSposgroup".

include "CoRN.ma".

(* $Id: QSposgroup.v,v 1.6 2004/04/08 08:20:32 lcf Exp $ *)

include "model/monoids/QSposmonoid.ma".

include "algebra/CGroups.ma".

(*#* **Example of a group: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
The positive rationals form with the operation  $(x,y) \mapsto xy/2$ 
#(x,y) &#x21A6; xy/2# a CGroup.
*)

inline "cic:/CoRN/model/groups/QSposgroup/Qpos_multdiv2_is_CGroup.con".

inline "cic:/CoRN/model/groups/QSposgroup/Qpos_multdiv2_as_CGroup.con".

