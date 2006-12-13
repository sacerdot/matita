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

include "CoRN.ma".

(* $Id: DerivativeOps.v,v 1.3 2004/04/23 10:00:58 lcf Exp $ *)

include "ftc/Derivative.ma".

(* UNEXPORTED
Section Lemmas
*)

(*#* **Algebraic Operations

We will now prove the main results about deriving functions built from
the algebraic operators#. #%\footnote{%Composition presents some
tricky questions, and is therefore discussed in a separated
context.%}.%

[F'] and [G'] will be the derivatives, respectively, of [F] and [G].

We begin with some technical stuff that will be necessary for division.
*)

alias id "a" = "cic:/CoRN/ftc/DerivativeOps/Lemmas/a.var".

alias id "b" = "cic:/CoRN/ftc/DerivativeOps/Lemmas/b.var".

alias id "Hab" = "cic:/CoRN/ftc/DerivativeOps/Lemmas/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Lemmas/I.con" "Lemmas__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/DerivativeOps/Lemmas/F.var".

(* begin hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Lemmas/P.con" "Lemmas__".

(* end hide *)

(* begin show *)

alias id "Fbnd" = "cic:/CoRN/ftc/DerivativeOps/Lemmas/Fbnd.var".

(* end show *)

inline "cic:/CoRN/ftc/DerivativeOps/bnd_away_zero_square.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Hint Resolve bnd_away_zero_square: included.
*)

(* UNEXPORTED
Section Local_Results
*)

(*#* **Local Results

We can now derive all the usual rules for deriving constant and identity functions, sums, inverses and products of functions with a known derivative.
*)

alias id "a" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Local_Results/Hab.con" "Local_Results__".

inline "cic:/CoRN/ftc/DerivativeOps/Local_Results/I.con" "Local_Results__".

(* end hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_const.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_id.con".

alias id "F" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/F.var".

alias id "F'" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/F'.var".

alias id "G" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/G.var".

alias id "G'" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/G'.var".

alias id "derF" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/derF.var".

alias id "derG" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/derG.var".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_plus.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_inv.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_mult.con".

(*#*
As was the case for continuity, the rule for the reciprocal function has a side condition.
*)

(* begin show *)

alias id "Fbnd" = "cic:/CoRN/ftc/DerivativeOps/Local_Results/Fbnd.var".

(* end show *)

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_recip.con".

(* UNEXPORTED
End Local_Results
*)

(* UNEXPORTED
Hint Immediate derivative_imp_inc derivative_imp_inc': included.
*)

(* UNEXPORTED
Hint Resolve Derivative_I_const Derivative_I_id Derivative_I_plus
  Derivative_I_inv Derivative_I_mult Derivative_I_recip: derivate.
*)

(* UNEXPORTED
Section Corolaries
*)

alias id "a" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/a.var".

alias id "b" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Corolaries/Hab.con" "Corolaries__".

inline "cic:/CoRN/ftc/DerivativeOps/Corolaries/I.con" "Corolaries__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/F.var".

alias id "F'" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/F'.var".

alias id "G" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/G.var".

alias id "G'" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/G'.var".

alias id "derF" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/derF.var".

alias id "derG" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/derG.var".

(*#*
From this lemmas the rules for the other algebraic operations follow directly.
*)

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_minus.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_scal.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_nth.con".

alias id "Gbnd" = "cic:/CoRN/ftc/DerivativeOps/Corolaries/Gbnd.var".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_div.con".

(* UNEXPORTED
End Corolaries
*)

(* UNEXPORTED
Hint Resolve Derivative_I_minus Derivative_I_nth Derivative_I_scal
  Derivative_I_div: derivate.
*)

(* UNEXPORTED
Section Derivative_Sums
*)

(*#* The derivation rules for families of functions are easily proved by
induction using the constant and addition rules.
*)

alias id "a" = "cic:/CoRN/ftc/DerivativeOps/Derivative_Sums/a.var".

alias id "b" = "cic:/CoRN/ftc/DerivativeOps/Derivative_Sums/b.var".

alias id "Hab" = "cic:/CoRN/ftc/DerivativeOps/Derivative_Sums/Hab.var".

alias id "Hab'" = "cic:/CoRN/ftc/DerivativeOps/Derivative_Sums/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_Sums/I.con" "Derivative_Sums__".

(* end hide *)

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sum0.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sumx.con".

inline "cic:/CoRN/ftc/DerivativeOps/Derivative_I_Sum.con".

(* UNEXPORTED
End Derivative_Sums
*)

(* UNEXPORTED
Hint Resolve Derivative_I_Sum0 Derivative_I_Sum Derivative_I_Sumx: derivate.
*)

