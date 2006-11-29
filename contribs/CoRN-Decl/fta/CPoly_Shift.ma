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

set "baseuri" "cic:/matita/CoRN-Decl/fta/CPoly_Shift".

include "CoRN.ma".

(* $Id: CPoly_Shift.v,v 1.4 2004/04/23 10:00:56 lcf Exp $ *)

include "complex/CComplex.ma".

(*#* * Shifting polynomials
This can be done for [CRings] in general, but we do it here
only for [CC] because extensionality makes everything much easier,
and we only need it for [CC].
*)

(* UNEXPORTED
Section Poly_Shifted
*)

inline "cic:/CoRN/fta/CPoly_Shift/Shift.con".

inline "cic:/CoRN/fta/CPoly_Shift/Shift_apply.con".

(* UNEXPORTED
Hint Resolve Shift_apply: algebra.
*)

inline "cic:/CoRN/fta/CPoly_Shift/Shift_wdr.con".

inline "cic:/CoRN/fta/CPoly_Shift/Shift_shift.con".

inline "cic:/CoRN/fta/CPoly_Shift/Shift_mult.con".

inline "cic:/CoRN/fta/CPoly_Shift/Shift_degree_le.con".

inline "cic:/CoRN/fta/CPoly_Shift/Shift_monic.con".

(* UNEXPORTED
End Poly_Shifted
*)

(* UNEXPORTED
Hint Resolve Shift_wdr: algebra_c.
*)

(* UNEXPORTED
Hint Resolve Shift_apply Shift_shift Shift_mult: algebra.
*)

