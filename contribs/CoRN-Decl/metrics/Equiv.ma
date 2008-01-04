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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/Equiv".

include "CoRN.ma".

(* $Id: Equiv.v,v 1.4 2004/04/23 10:01:02 lcf Exp $ *)

include "metrics/IR_CPMSpace.ma".

(* UNEXPORTED
Section equivalent
*)

(*#* **Equivalent Pseudo Metric Spaces
*)

(*#*
We say that two pseudo metric spaces are equivalent, when there exists a 
bijective, structure-preserving function between them.
*)

inline "cic:/CoRN/metrics/Equiv/equivalent_psmetric.con".

inline "cic:/CoRN/metrics/Equiv/isopsmetry.con".

(* UNEXPORTED
Implicit Arguments isopsmetry [X Y].
*)

inline "cic:/CoRN/metrics/Equiv/isopsmetry_imp_bij.con".

inline "cic:/CoRN/metrics/Equiv/isopsmetry_imp_lipschitz.con".

inline "cic:/CoRN/metrics/Equiv/id_is_isopsmetry.con".

inline "cic:/CoRN/metrics/Equiv/comp_resp_isopsmetry.con".

inline "cic:/CoRN/metrics/Equiv/inv_isopsmetry.con".

inline "cic:/CoRN/metrics/Equiv/MSequivalent.con".

(*#*
Not all pseudo metric spaces are equivalent:
*)

inline "cic:/CoRN/metrics/Equiv/MSequivalent_discr.con".

(* UNEXPORTED
End equivalent
*)

