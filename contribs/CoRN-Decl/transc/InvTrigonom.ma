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

set "baseuri" "cic:/matita/CoRN-Decl/transc/InvTrigonom".

include "CoRN.ma".

(* $Id: InvTrigonom.v,v 1.9 2004/04/23 10:01:07 lcf Exp $ *)

include "transc/RealPowers.ma".

include "transc/TrigMon.ma".

include "ftc/StrongIVT.ma".

(*#* printing ArcSin %\ensuremath{\arcsin}% *)

(*#* printing ArcCos %\ensuremath{\arccos}% *)

(*#* printing ArcTan %\ensuremath{\arctan}% *)

(*#* *Inverse Trigonometric Functions

**Definitions

We will now define arcsine, arccosine and arctangent as indefinite
integrals and prove their main properties.  We begin by proving that
the appropriate indefinite integrals can be defined, then prove the
main properties of the function.

Arccosine is defined in terms of arcsine by the relation
[ArcCos(x)=Pi[/]Two-ArcSin(x)].

***Arcsine
*)

(* UNEXPORTED
Opaque Sine Cosine Expon Logarithm.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_def_lemma.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_def_zero.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcSin.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_domain.con".

inline "cic:/CoRN/transc/InvTrigonom/Continuous_ArcSin.con".

inline "cic:/CoRN/transc/InvTrigonom/Derivative_ArcSin.con".

(* UNEXPORTED
Hint Resolve Derivative_ArcSin: derivate.
*)

(* UNEXPORTED
Hint Resolve Continuous_ArcSin: continuous.
*)

(*#* ***Arccosine
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcCos.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcCos_domain.con".

inline "cic:/CoRN/transc/InvTrigonom/Continuous_ArcCos.con".

inline "cic:/CoRN/transc/InvTrigonom/Derivative_ArcCos.con".

(*#* ***Arctangent
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_def_lemma.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcTang.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_domain.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcTan.con".

inline "cic:/CoRN/transc/InvTrigonom/Continuous_ArcTan.con".

inline "cic:/CoRN/transc/InvTrigonom/Derivative_ArcTan.con".

(* UNEXPORTED
Hint Resolve Derivative_ArcCos Derivative_ArcTan: derivate.
*)

(* UNEXPORTED
Hint Resolve Continuous_ArcCos Continuous_ArcTan: continuous.
*)

(* UNEXPORTED
Section Inverses
*)

(*#* **Composition properties

We now prove that this functions are in fact inverses to the corresponding trigonometric functions.

***Sine and Arcsine
*)

inline "cic:/CoRN/transc/InvTrigonom/maps_Sin.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_Sin_inv.con".

(* UNEXPORTED
Opaque ArcSin.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_Sin.con".

(* UNEXPORTED
Transparent ArcSin.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_range.con".

(* UNEXPORTED
Transparent ArcSin.
*)

inline "cic:/CoRN/transc/InvTrigonom/Sin_ArcSin.con".

inline "cic:/CoRN/transc/InvTrigonom/Sin_ArcSin_inv.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcSin_resp_leEq.con".

(*#* ***Cosine and Arcosine
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcCos_Cos.con".

inline "cic:/CoRN/transc/InvTrigonom/Cos_ArcCos.con".

inline "cic:/CoRN/transc/InvTrigonom/ArcCos_Cos_inv.con".

inline "cic:/CoRN/transc/InvTrigonom/Cos_ArcCos_inv.con".

(* UNEXPORTED
Opaque ArcSin.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcCos_resp_leEq.con".

(*#* ***Tangent and Arctangent
*)

inline "cic:/CoRN/transc/InvTrigonom/maps_Tan.con".

(* UNEXPORTED
Opaque Tang.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_Tan_inv.con".

(* UNEXPORTED
Transparent Tang.
*)

(* UNEXPORTED
Opaque ArcTang.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_Tan.con".

(* UNEXPORTED
Opaque iprop.
*)

(* UNEXPORTED
Transparent iprop.
*)

(* UNEXPORTED
Opaque Cos.
*)

inline "cic:/CoRN/transc/InvTrigonom/Tan_ilim.con".

(* UNEXPORTED
Opaque Min.
*)

(* UNEXPORTED
Transparent Cos.
*)

(* UNEXPORTED
Section ArcTan_Range
*)

alias id "x" = "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/x.var".

(* begin hide *)

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min1.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min2.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min3.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min4.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max1.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max2.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max3.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max4.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min5.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/min6.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max5.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/max6.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a1.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a2.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a3.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a4.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/a5.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b1.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b2.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b3.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b4.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/b5.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/Inverses/ArcTan_Range/ab.con" "Inverses__ArcTan_Range__".

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_range_lemma.con".

(* end hide *)

(* UNEXPORTED
Transparent ArcTang.
*)

inline "cic:/CoRN/transc/InvTrigonom/ArcTan_range.con".

(* UNEXPORTED
End ArcTan_Range
*)

(* UNEXPORTED
Transparent ArcTang.
*)

inline "cic:/CoRN/transc/InvTrigonom/Tan_ArcTan.con".

(* UNEXPORTED
Opaque ArcTang.
*)

inline "cic:/CoRN/transc/InvTrigonom/Tan_ArcTan_inv.con".

(* UNEXPORTED
End Inverses
*)

