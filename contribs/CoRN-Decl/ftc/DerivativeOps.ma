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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/DerivativeOps".

(* $Id: DerivativeOps.v,v 1.3 2004/04/23 10:00:58 lcf Exp $ *)

(* INCLUDE
Derivative
*)

(* UNEXPORTED
Section Lemmas.
*)

(*#* **Algebraic Operations

We will now prove the main results about deriving functions built from
the algebraic operators#. #%\footnote{%Composition presents some
tricky questions, and is therefore discussed in a separated
context.%}.%

[F'] and [G'] will be the derivatives, respectively, of [F] and [G].

We begin with some technical stuff that will be necessary for division.
*)

inline cic:/CoRN/ftc/DerivativeOps/a.var.

inline cic:/CoRN/ftc/DerivativeOps/b.var.

inline cic:/CoRN/ftc/DerivativeOps/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/DerivativeOps/I.con.

(* end hide *)

inline cic:/CoRN/ftc/DerivativeOps/F.var.

(* begin hide *)

inline cic:/CoRN/ftc/DerivativeOps/P.con.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/DerivativeOps/Fbnd.var.

(* end show *)

inline cic:/CoRN/ftc/DerivativeOps/bnd_away_zero_square.con.

(* UNEXPORTED
End Lemmas.
*)

(* UNEXPORTED
Hint Resolve bnd_away_zero_square: included.
*)

(* UNEXPORTED
Section Local_Results.
*)

(*#* **Local Results

We can now derive all the usual rules for deriving constant and identity functions, sums, inverses and products of functions with a known derivative.
*)

inline cic:/CoRN/ftc/DerivativeOps/a.var.

inline cic:/CoRN/ftc/DerivativeOps/b.var.

inline cic:/CoRN/ftc/DerivativeOps/Hab'.var.

(* begin hide *)

inline cic:/CoRN/ftc/DerivativeOps/Hab.con.

inline cic:/CoRN/ftc/DerivativeOps/I.con.

(* end hide *)

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_const.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_id.con.

inline cic:/CoRN/ftc/DerivativeOps/F.var.

inline cic:/CoRN/ftc/DerivativeOps/F'.var.

inline cic:/CoRN/ftc/DerivativeOps/G.var.

inline cic:/CoRN/ftc/DerivativeOps/G'.var.

inline cic:/CoRN/ftc/DerivativeOps/derF.var.

inline cic:/CoRN/ftc/DerivativeOps/derG.var.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_plus.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_inv.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_mult.con.

(*#*
As was the case for continuity, the rule for the reciprocal function has a side condition.
*)

(* begin show *)

inline cic:/CoRN/ftc/DerivativeOps/Fbnd.var.

(* end show *)

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_recip.con.

(* UNEXPORTED
End Local_Results.
*)

(* UNEXPORTED
Hint Immediate derivative_imp_inc derivative_imp_inc': included.
*)

(* UNEXPORTED
Hint Resolve Derivative_I_const Derivative_I_id Derivative_I_plus
  Derivative_I_inv Derivative_I_mult Derivative_I_recip: derivate.
*)

(* UNEXPORTED
Section Corolaries.
*)

inline cic:/CoRN/ftc/DerivativeOps/a.var.

inline cic:/CoRN/ftc/DerivativeOps/b.var.

inline cic:/CoRN/ftc/DerivativeOps/Hab'.var.

(* begin hide *)

inline cic:/CoRN/ftc/DerivativeOps/Hab.con.

inline cic:/CoRN/ftc/DerivativeOps/I.con.

(* end hide *)

inline cic:/CoRN/ftc/DerivativeOps/F.var.

inline cic:/CoRN/ftc/DerivativeOps/F'.var.

inline cic:/CoRN/ftc/DerivativeOps/G.var.

inline cic:/CoRN/ftc/DerivativeOps/G'.var.

inline cic:/CoRN/ftc/DerivativeOps/derF.var.

inline cic:/CoRN/ftc/DerivativeOps/derG.var.

(*#*
From this lemmas the rules for the other algebraic operations follow directly.
*)

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_minus.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_scal.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_nth.con.

inline cic:/CoRN/ftc/DerivativeOps/Gbnd.var.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_div.con.

(* UNEXPORTED
End Corolaries.
*)

(* UNEXPORTED
Hint Resolve Derivative_I_minus Derivative_I_nth Derivative_I_scal
  Derivative_I_div: derivate.
*)

(* UNEXPORTED
Section Derivative_Sums.
*)

(*#* The derivation rules for families of functions are easily proved by
induction using the constant and addition rules.
*)

inline cic:/CoRN/ftc/DerivativeOps/a.var.

inline cic:/CoRN/ftc/DerivativeOps/b.var.

inline cic:/CoRN/ftc/DerivativeOps/Hab.var.

inline cic:/CoRN/ftc/DerivativeOps/Hab'.var.

(* begin hide *)

inline cic:/CoRN/ftc/DerivativeOps/I.con.

(* end hide *)

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sum0.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sumx.con.

inline cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sum.con.

(* UNEXPORTED
End Derivative_Sums.
*)

(* UNEXPORTED
Hint Resolve Derivative_I_Sum0 Derivative_I_Sum Derivative_I_Sumx: derivate.
*)

