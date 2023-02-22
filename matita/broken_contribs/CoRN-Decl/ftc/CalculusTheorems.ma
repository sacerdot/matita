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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/CalculusTheorems".

include "CoRN.ma".

(* $Id: CalculusTheorems.v,v 1.6 2004/04/23 10:00:57 lcf Exp $ *)

include "ftc/Rolle.ma".

include "tactics/DiffTactics3.ma".

(* UNEXPORTED
Opaque Min Max.
*)

(* UNEXPORTED
Section Various_Theorems
*)

(*#* *Calculus Theorems

This file is intended to present a collection of miscellaneous, mostly
technical results in differential calculus that are interesting or
useful in future work.

We begin with some properties of continuous functions.  Every
continuous function commutes with the limit of a numerical sequence
(sometimes called Heine continuity).
*)

inline "cic:/CoRN/ftc/CalculusTheorems/Continuous_imp_comm_Lim.con".

(*#*
This is a tricky result: if [F] is continuous and positive in both [[a,b]]
and [(b,c]], then it is positive in [[a,c]].
*)

inline "cic:/CoRN/ftc/CalculusTheorems/Continuous_imp_pos.con".

(*#*
Similar results for increasing functions:
*)

inline "cic:/CoRN/ftc/CalculusTheorems/strict_inc_glues.con".

inline "cic:/CoRN/ftc/CalculusTheorems/strict_inc_glues'.con".

inline "cic:/CoRN/ftc/CalculusTheorems/strict_dec_glues.con".

inline "cic:/CoRN/ftc/CalculusTheorems/strict_dec_glues'.con".

(*#* More on glueing intervals. *)

inline "cic:/CoRN/ftc/CalculusTheorems/olor_pos_clor_nonneg.con".

inline "cic:/CoRN/ftc/CalculusTheorems/olor_pos_olcr_nonneg.con".

inline "cic:/CoRN/ftc/CalculusTheorems/olor_pos_clcr_nonneg.con".

(*#*
Any function that has the null function as its derivative must be constant.
*)

inline "cic:/CoRN/ftc/CalculusTheorems/FConst_prop.con".

(*#* As a corollary, two functions with the same derivative must differ
by a constant.
*)

inline "cic:/CoRN/ftc/CalculusTheorems/Feq_crit_with_const.con".

(*#* This yields the following known result: any differential equation
of the form [f'=g] with initial condition [f(a) [=] b] has a unique solution.
*)

inline "cic:/CoRN/ftc/CalculusTheorems/Feq_criterium.con".

(*#*
Finally, a well known result: any function with a (strictly) positive
derivative is (strictly) increasing.  Although the two lemmas look
quite similar the proofs are completely different, both from the
formalization and from the mathematical point of view.
*)

inline "cic:/CoRN/ftc/CalculusTheorems/Derivative_imp_resp_less.con".

inline "cic:/CoRN/ftc/CalculusTheorems/Derivative_imp_resp_leEq.con".

inline "cic:/CoRN/ftc/CalculusTheorems/Derivative_imp_resp_less'.con".

(*#* From these results we can finally prove that exponentiation to a
real power preserves the less or equal than relation!
*)

(* UNEXPORTED
Opaque nring.
*)

(* UNEXPORTED
Transparent nring.
*)

inline "cic:/CoRN/ftc/CalculusTheorems/nexp_resp_leEq_odd.con".

(* UNEXPORTED
End Various_Theorems
*)

