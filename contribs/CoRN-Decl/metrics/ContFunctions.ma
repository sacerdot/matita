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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/ContFunctions".

include "CoRN.ma".

(* $Id: ContFunctions.v,v 1.3 2004/04/23 10:01:02 lcf Exp $ *)

include "metrics/CPseudoMSpaces.ma".

(* UNEXPORTED
Section Continuous_functions
*)

(*#* **Continuous functions, uniformly continuous functions and Lipschitz functions
%\begin{convention}%
Let [A] and [B] be pseudo metric spaces.
%\end{convention}%
*)

alias id "A" = "cic:/CoRN/metrics/ContFunctions/Continuous_functions/A.var".

alias id "B" = "cic:/CoRN/metrics/ContFunctions/Continuous_functions/B.var".

(*#*
We will look at some notions of continuous functions.
*)

inline "cic:/CoRN/metrics/ContFunctions/continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/continuous'.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous'.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous''.con".

inline "cic:/CoRN/metrics/ContFunctions/lipschitz.con".

inline "cic:/CoRN/metrics/ContFunctions/lipschitz'.con".

(* UNEXPORTED
End Continuous_functions
*)

(* UNEXPORTED
Implicit Arguments continuous [A B].
*)

(* UNEXPORTED
Implicit Arguments uni_continuous [A B].
*)

(* UNEXPORTED
Implicit Arguments lipschitz [A B].
*)

(* UNEXPORTED
Implicit Arguments continuous' [A B].
*)

(* UNEXPORTED
Implicit Arguments uni_continuous' [A B].
*)

(* UNEXPORTED
Implicit Arguments uni_continuous'' [A B].
*)

(* UNEXPORTED
Implicit Arguments lipschitz' [A B].
*)

(* UNEXPORTED
Section Lemmas
*)

(* begin hide *)

inline "cic:/CoRN/metrics/ContFunctions/nexp_power.con".

(* end hide *)

inline "cic:/CoRN/metrics/ContFunctions/continuous_imp_continuous'.con".

inline "cic:/CoRN/metrics/ContFunctions/continuous'_imp_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous_imp_uni_continuous'.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous'_imp_uni_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous'_imp_uni_continuous''.con".

inline "cic:/CoRN/metrics/ContFunctions/lipschitz_imp_lipschitz'.con".

inline "cic:/CoRN/metrics/ContFunctions/lipschitz'_imp_lipschitz.con".

(*#*
Every uniformly continuous function is continuous and 
every Lipschitz function is uniformly continuous.
*)

inline "cic:/CoRN/metrics/ContFunctions/uni_continuous_imp_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/lipschitz_imp_uni_continuous.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Section Identity
*)

(*#* **Identity 
*)

(*#*
The identity function is Lipschitz. 
Hence it is uniformly continuous and continuous.
*)

inline "cic:/CoRN/metrics/ContFunctions/id_is_lipschitz.con".

inline "cic:/CoRN/metrics/ContFunctions/id_is_uni_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/id_is_continuous.con".

(* UNEXPORTED
End Identity
*)

(* UNEXPORTED
Section Constant
*)

(*#* **Constant functions
%\begin{convention}%
Let [B] and [X] be pseudo metric spaces.
%\end{convention}%
*)

(*#*
Any constant function is Lipschitz. 
Hence it is uniformly continuous and continuous.
*)

alias id "B" = "cic:/CoRN/metrics/ContFunctions/Constant/B.var".

alias id "X" = "cic:/CoRN/metrics/ContFunctions/Constant/X.var".

inline "cic:/CoRN/metrics/ContFunctions/const_fun_is_lipschitz.con".

inline "cic:/CoRN/metrics/ContFunctions/const_fun_is_uni_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/const_fun_is_continuous.con".

(* UNEXPORTED
End Constant
*)

(* UNEXPORTED
Section Composition
*)

(*#* **Composition
%\begin{convention}%
Let [B],[C] and [X] be pseudo metric spaces.
Let [f : (CSetoid_fun X B)] and
[g : (CSetoid_fun  B C)].
%\end{convention}%
*)

(*#*
The composition of two Lipschitz/uniformly continous/continuous functions is 
again Lipschitz/uniformly continuous/continuous.
*)

alias id "X" = "cic:/CoRN/metrics/ContFunctions/Composition/X.var".

alias id "B" = "cic:/CoRN/metrics/ContFunctions/Composition/B.var".

alias id "f" = "cic:/CoRN/metrics/ContFunctions/Composition/f.var".

alias id "C" = "cic:/CoRN/metrics/ContFunctions/Composition/C.var".

alias id "g" = "cic:/CoRN/metrics/ContFunctions/Composition/g.var".

inline "cic:/CoRN/metrics/ContFunctions/comp_resp_lipschitz.con".

inline "cic:/CoRN/metrics/ContFunctions/comp_resp_uni_continuous.con".

inline "cic:/CoRN/metrics/ContFunctions/comp_resp_continuous.con".

(* UNEXPORTED
End Composition
*)

(* UNEXPORTED
Section Limit
*)

(*#* **Limit
*)

inline "cic:/CoRN/metrics/ContFunctions/MSseqLimit.con".

(* UNEXPORTED
Implicit Arguments MSseqLimit [X].
*)

inline "cic:/CoRN/metrics/ContFunctions/MSseqLimit'.con".

(* UNEXPORTED
Implicit Arguments MSseqLimit' [X].
*)

inline "cic:/CoRN/metrics/ContFunctions/MSseqLimit_imp_MSseqLimit'.con".

inline "cic:/CoRN/metrics/ContFunctions/MSseqLimit'_imp_MSseqLimit.con".

inline "cic:/CoRN/metrics/ContFunctions/seqcontinuous'.con".

(* UNEXPORTED
Implicit Arguments seqcontinuous' [A B].
*)

inline "cic:/CoRN/metrics/ContFunctions/continuous'_imp_seqcontinuous'.con".

(* UNEXPORTED
End Limit
*)

