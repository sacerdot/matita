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

set "baseuri" "cic:/matita/CoRN-Decl/reals/OddPolyRootIR".

include "CoRN.ma".

(* $Id: OddPolyRootIR.v,v 1.5 2004/04/23 10:01:05 lcf Exp $ *)

include "reals/IVT.ma".

(*#* * Roots of polynomials of odd degree *)

(* UNEXPORTED
Section CPoly_Big
*)

(*#* ** Monic polynomials are positive near infinity
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/reals/OddPolyRootIR/CPoly_Big/R.var".

(* begin hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/CPoly_Big/RX.con" "CPoly_Big__".

(* end hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/Cbigger.con".

inline "cic:/CoRN/reals/OddPolyRootIR/Ccpoly_big.con".

inline "cic:/CoRN/reals/OddPolyRootIR/cpoly_pos.con".

inline "cic:/CoRN/reals/OddPolyRootIR/Ccpoly_pos'.con".

(* UNEXPORTED
End CPoly_Big
*)

(* UNEXPORTED
Section Flip_Poly
*)

(*#* **Flipping a polynomial
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/reals/OddPolyRootIR/Flip_Poly/R.var".

(* begin hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/Flip_Poly/RX.con" "Flip_Poly__".

(* end hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/flip.con".

inline "cic:/CoRN/reals/OddPolyRootIR/flip_poly.con".

inline "cic:/CoRN/reals/OddPolyRootIR/flip_coefficient.con".

(* UNEXPORTED
Hint Resolve flip_coefficient: algebra.
*)

inline "cic:/CoRN/reals/OddPolyRootIR/flip_odd.con".

(* UNEXPORTED
End Flip_Poly
*)

(* UNEXPORTED
Hint Resolve flip_poly: algebra.
*)

(* UNEXPORTED
Section OddPoly_Signs
*)

(*#* ** Sign of a polynomial of odd degree
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/reals/OddPolyRootIR/OddPoly_Signs/R.var".

(* begin hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/OddPoly_Signs/RX.con" "OddPoly_Signs__".

(* end hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/oddpoly_pos.con".

inline "cic:/CoRN/reals/OddPolyRootIR/oddpoly_pos'.con".

inline "cic:/CoRN/reals/OddPolyRootIR/oddpoly_neg.con".

(* UNEXPORTED
End OddPoly_Signs
*)

(* UNEXPORTED
Section Poly_Norm
*)

(*#* ** The norm of a polynomial
%\begin{convention}% Let [R] be a field, and [RX] the polynomials over
this field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/reals/OddPolyRootIR/Poly_Norm/R.var".

(* begin hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/Poly_Norm/RX.con" "Poly_Norm__".

(* end hide *)

inline "cic:/CoRN/reals/OddPolyRootIR/poly_norm_aux.con".

inline "cic:/CoRN/reals/OddPolyRootIR/poly_norm.con".

inline "cic:/CoRN/reals/OddPolyRootIR/poly_norm_monic.con".

inline "cic:/CoRN/reals/OddPolyRootIR/poly_norm_apply.con".

(* UNEXPORTED
End Poly_Norm
*)

(* UNEXPORTED
Section OddPoly_Root
*)

(*#* ** Roots of polynomials of odd degree
Polynomials of odd degree over the reals always have a root. *)

inline "cic:/CoRN/reals/OddPolyRootIR/oddpoly_root'.con".

inline "cic:/CoRN/reals/OddPolyRootIR/oddpoly_root.con".

inline "cic:/CoRN/reals/OddPolyRootIR/realpolyn_oddhaszero.con".

(* UNEXPORTED
End OddPoly_Root
*)

