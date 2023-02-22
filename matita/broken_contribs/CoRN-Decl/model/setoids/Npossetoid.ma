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

set "baseuri" "cic:/matita/CoRN-Decl/model/setoids/Npossetoid".

include "CoRN.ma".

(* $Id: Npossetoid.v,v 1.3 2004/04/06 15:46:04 lcf Exp $ *)

include "model/setoids/Nsetoid.ma".

include "model/structures/Npossec.ma".

include "algebra/CSetoidFun.ma".

(*#* **Example of a setoid: [Npos]

*** Setoid
The positive natural numbers [Npos] will be defined as a subsetoid of the
natural numbers.
*)

inline "cic:/CoRN/model/setoids/Npossetoid/Npos.con".

inline "cic:/CoRN/model/setoids/Npossetoid/NposP.con".

(*#* One and two are elements of it.
*)

inline "cic:/CoRN/model/setoids/Npossetoid/ONEpos.con".

inline "cic:/CoRN/model/setoids/Npossetoid/TWOpos.con".

(*#* ***Addition and multiplication
Because addition and multiplication preserve positivity, we can define 
them on this subsetoid.
*)

inline "cic:/CoRN/model/setoids/Npossetoid/plus_resp_Npos.con".

inline "cic:/CoRN/model/setoids/Npossetoid/Npos_plus.con".

inline "cic:/CoRN/model/setoids/Npossetoid/mult_resp_Npos.con".

inline "cic:/CoRN/model/setoids/Npossetoid/Npos_mult.con".

(*#* The addition has no right unit on this set.
*)

inline "cic:/CoRN/model/setoids/Npossetoid/no_rht_unit_Npos1.con".

(*#* And the multiplication doesn't have an inverse, because there can't be an
inverse for 2.
*)

inline "cic:/CoRN/model/setoids/Npossetoid/no_inverse_Nposmult1.con".

