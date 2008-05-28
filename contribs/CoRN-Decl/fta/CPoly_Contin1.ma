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

set "baseuri" "cic:/matita/CoRN-Decl/fta/CPoly_Contin1".

include "CoRN.ma".

(* $Id: CPoly_Contin1.v,v 1.3 2004/04/23 10:00:56 lcf Exp $ *)

include "fta/CC_Props.ma".

(*#* * Continuity of complex polynomials
*)

(* UNEXPORTED
Section Mult_CC_Continuous
*)

inline "cic:/CoRN/fta/CPoly_Contin1/mult_absCC.con".

inline "cic:/CoRN/fta/CPoly_Contin1/estimate_absCC.con".

inline "cic:/CoRN/fta/CPoly_Contin1/mult_CC_contin.con".

(* UNEXPORTED
End Mult_CC_Continuous
*)

(* UNEXPORTED
Section CPoly_CC_Continuous
*)

(*#*
%\begin{convention}% Let [g] be a polynomial over the complex numbers.
%\end{convention}%
*)

alias id "g" = "cic:/CoRN/fta/CPoly_Contin1/CPoly_CC_Continuous/g.var".

inline "cic:/CoRN/fta/CPoly_Contin1/cpoly_CC_contin.con".

inline "cic:/CoRN/fta/CPoly_Contin1/contin_polyCC.con".

(* UNEXPORTED
End CPoly_CC_Continuous
*)

