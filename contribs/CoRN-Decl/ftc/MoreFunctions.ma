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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/MoreFunctions".

include "CoRN.ma".

(* $Id: MoreFunctions.v,v 1.5 2004/04/20 22:38:50 hinderer Exp $ *)

(*#* printing FNorm %\ensuremath{\|\cdot\|_{\infty}}% *)

include "ftc/MoreIntervals.ma".

(* UNEXPORTED
Opaque Min Max.
*)

(* UNEXPORTED
Section Basic_Results
*)

(*#* *More about Functions

Here we state all the main results about properties of functions that
we already proved for compact intervals in the more general setting of
arbitrary intervals.

%\begin{convention}% Let [I:interval] and [F,F',G,G'] be partial functions.
%\end{convention}%

**Continuity
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Basic_Results/I.var".

(*#*
Trivial stuff.
*)

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_imp_inc.con".

(*#*
%\begin{convention}% Assume that [I] is compact and [F] is continuous in [I].
%\end{convention}%
*)

alias id "cI" = "cic:/CoRN/ftc/MoreFunctions/Basic_Results/cI.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Basic_Results/F.var".

alias id "contF" = "cic:/CoRN/ftc/MoreFunctions/Basic_Results/contF.var".

inline "cic:/CoRN/ftc/MoreFunctions/continuous_compact.con".

(* begin show *)

alias id "Hinc" = "cic:/CoRN/ftc/MoreFunctions/Basic_Results/Hinc.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_I_imp_tb_image.con".

inline "cic:/CoRN/ftc/MoreFunctions/FNorm.con".

inline "cic:/CoRN/ftc/MoreFunctions/FNorm_bnd_AbsIR.con".

(* UNEXPORTED
End Basic_Results
*)

(* UNEXPORTED
Hint Resolve Continuous_imp_inc: included.
*)

(* UNEXPORTED
Section Other_Results
*)

(*#*
The usual stuff.
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Other_Results/I.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Other_Results/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/Other_Results/G.var".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_wd.con".

(* begin show *)

alias id "contF" = "cic:/CoRN/ftc/MoreFunctions/Other_Results/contF.var".

alias id "contG" = "cic:/CoRN/ftc/MoreFunctions/Other_Results/contG.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunctions/included_imp_Continuous.con".

inline "cic:/CoRN/ftc/MoreFunctions/Included_imp_Continuous.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_const.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_id.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_plus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_inv.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_minus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_mult.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_nth.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_scal.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_abs.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_recip.con".

(* UNEXPORTED
End Other_Results
*)

(* UNEXPORTED
Hint Resolve continuous_compact Continuous_const Continuous_id
  Continuous_plus Continuous_inv Continuous_minus Continuous_mult
  Continuous_scal Continuous_nth Continuous_recip Continuous_abs: continuous.
*)

(* UNEXPORTED
Hint Immediate included_imp_Continuous Included_imp_Continuous: continuous.
*)

(* UNEXPORTED
Section Corollaries
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/I.var".

alias id "cI" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/cI.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/G.var".

alias id "contF" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/contF.var".

alias id "contG" = "cic:/CoRN/ftc/MoreFunctions/Corollaries/contG.var".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_div.con".

inline "cic:/CoRN/ftc/MoreFunctions/FNorm_wd.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
Hint Resolve Continuous_div: continuous.
*)

(* UNEXPORTED
Section Sums
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Sums/I.var".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_Sumx.con".

(*#*
%\begin{convention}% Assume [f] is a sequence of continuous functions.
%\end{convention}%
*)

alias id "f" = "cic:/CoRN/ftc/MoreFunctions/Sums/f.var".

alias id "contF" = "cic:/CoRN/ftc/MoreFunctions/Sums/contF.var".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_Sum0.con".

inline "cic:/CoRN/ftc/MoreFunctions/Continuous_Sum.con".

(* UNEXPORTED
End Sums
*)

(* UNEXPORTED
Hint Resolve Continuous_Sum0 Continuous_Sumx Continuous_Sum: continuous.
*)

(* UNEXPORTED
Section Basic_Properties
*)

(*#* **Derivative

Derivative is not that much different.

%\begin{convention}% From this point on we assume [I] to be proper.
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Basic_Properties/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/Basic_Properties/pI.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Basic_Properties/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/Basic_Properties/G.var".

alias id "H" = "cic:/CoRN/ftc/MoreFunctions/Basic_Properties/H.var".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_wdl.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_wdr.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_unique.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_imp_inc.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_imp_inc'.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_imp_Continuous.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_imp_Continuous'.con".

(* UNEXPORTED
End Basic_Properties
*)

(* UNEXPORTED
Hint Immediate Derivative_imp_inc Derivative_imp_inc': included.
*)

(* UNEXPORTED
Hint Immediate Derivative_imp_Continuous Derivative_imp_Continuous':
  continuous.
*)

(* UNEXPORTED
Section More_Results
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/More_Results/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/More_Results/pI.var".

(*#*
%\begin{convention}% Assume that [F'] and [G'] are derivatives of [F] and [G], respectively, in [I].
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/More_Results/F.var".

alias id "F'" = "cic:/CoRN/ftc/MoreFunctions/More_Results/F'.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/More_Results/G.var".

alias id "G'" = "cic:/CoRN/ftc/MoreFunctions/More_Results/G'.var".

alias id "derF" = "cic:/CoRN/ftc/MoreFunctions/More_Results/derF.var".

alias id "derG" = "cic:/CoRN/ftc/MoreFunctions/More_Results/derG.var".

inline "cic:/CoRN/ftc/MoreFunctions/included_imp_Derivative.con".

inline "cic:/CoRN/ftc/MoreFunctions/Included_imp_Derivative.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_const.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_id.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_plus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_inv.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_minus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_mult.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_scal.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_nth.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_recip.con".

(* UNEXPORTED
End More_Results
*)

(* UNEXPORTED
Section More_Corollaries
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/pI.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/F.var".

alias id "F'" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/F'.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/G.var".

alias id "G'" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/G'.var".

alias id "derF" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/derF.var".

alias id "derG" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/derG.var".

(* begin show *)

alias id "Gbnd" = "cic:/CoRN/ftc/MoreFunctions/More_Corollaries/Gbnd.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_div.con".

(* UNEXPORTED
End More_Corollaries
*)

(* UNEXPORTED
Section More_Sums
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/More_Sums/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/More_Sums/pI.var".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_Sumx.con".

(* begin show *)

alias id "f" = "cic:/CoRN/ftc/MoreFunctions/More_Sums/f.var".

alias id "f'" = "cic:/CoRN/ftc/MoreFunctions/More_Sums/f'.var".

alias id "derF" = "cic:/CoRN/ftc/MoreFunctions/More_Sums/derF.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_Sum0.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_Sum.con".

(* UNEXPORTED
End More_Sums
*)

(* UNEXPORTED
Section Diffble_Basic_Properties
*)

(*#* **Differentiability

Mutatis mutandis for differentiability.
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/pI.var".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_imp_inc.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_imp_Diffble.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_wd.con".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/G.var".

alias id "diffF" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/diffF.var".

alias id "diffG" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Basic_Properties/diffG.var".

(*#*
%\begin{convention}% Assume [F] and [G] are differentiable in [I].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/MoreFunctions/included_imp_Diffble.con".

inline "cic:/CoRN/ftc/MoreFunctions/Included_imp_Diffble.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_const.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_id.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_plus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_inv.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_minus.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_mult.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_nth.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_scal.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_recip.con".

(* UNEXPORTED
End Diffble_Basic_Properties
*)

(* UNEXPORTED
Hint Immediate Diffble_imp_inc: included.
*)

(* UNEXPORTED
Section Diffble_Corollaries
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/pI.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/G.var".

alias id "diffF" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/diffF.var".

alias id "diffG" = "cic:/CoRN/ftc/MoreFunctions/Diffble_Corollaries/diffG.var".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_div.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_Sum0.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_Sumx.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_Sum.con".

(* UNEXPORTED
End Diffble_Corollaries
*)

(* UNEXPORTED
Section Nth_Derivative
*)

(*#* **Nth Derivative

Higher order derivatives pose more interesting problems.  It turns out that it really becomes necessary to generalize our [n_deriv] operator to any interval.
*)

alias id "I" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/I.var".

alias id "pI" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/pI.var".

(* UNEXPORTED
Section Definitions
*)

(*#*
%\begin{convention}% Let [n:nat], [F:PartIR] and assume that [F] is n-times differentiable in [I].
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/Definitions/n.var".

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/Definitions/F.var".

alias id "diffF" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/Definitions/diffF.var".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_fun.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_char
 (* begin hide *).con".

(* end hide *)

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_strext.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_wd.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Section Basic_Results
*)

(*#*
All the usual results hold.
*)

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_n_wd.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_wdr.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_wdl.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_unique.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_n_imp_Diffble.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_Diffble.con".

inline "cic:/CoRN/ftc/MoreFunctions/le_imp_Diffble_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_n_imp_le.con".

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_n_imp_inc.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_Diffble_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_inc.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_inc'.con".

inline "cic:/CoRN/ftc/MoreFunctions/included_imp_Derivative_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/included_imp_Diffble_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Included_imp_Derivative_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Included_imp_Diffble_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_plus.con".

(* UNEXPORTED
End Basic_Results
*)

(* UNEXPORTED
Section More_Results
*)

(*#*
Some new results hold, too:
*)

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_Feq.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_lemma.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_S.con".

inline "cic:/CoRN/ftc/MoreFunctions/N_Deriv_plus.con".

(*#*
Some useful characterization results.
*)

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_O.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_Sn.con".

(* UNEXPORTED
End More_Results
*)

(* UNEXPORTED
Section Derivating_Diffble
*)

(*#*
As a special case we get a differentiation operator%\ldots%#...#
*)

alias id "F" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/Derivating_Diffble/F.var".

(* begin show *)

alias id "diffF" = "cic:/CoRN/ftc/MoreFunctions/Nth_Derivative/Derivating_Diffble/diffF.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunctions/Diffble_imp_Diffble_n.con".

inline "cic:/CoRN/ftc/MoreFunctions/Deriv.con".

(* UNEXPORTED
End Derivating_Diffble
*)

(* UNEXPORTED
Section Corollaries
*)

(*#*
%\ldots%#...# for which the expected property also holds.
*)

inline "cic:/CoRN/ftc/MoreFunctions/Deriv_lemma.con".

(*#*
Some more interesting properties.
*)

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_1.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_chain.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_Continuous.con".

inline "cic:/CoRN/ftc/MoreFunctions/Derivative_n_imp_Continuous'.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
End Nth_Derivative
*)

(* UNEXPORTED
Hint Resolve Derivative_const Derivative_id Derivative_plus Derivative_inv
  Derivative_minus Derivative_mult Derivative_scal Derivative_nth
  Derivative_recip Derivative_div Derivative_Sumx Derivative_Sum0
  Derivative_Sum: derivate.
*)

(* UNEXPORTED
Hint Immediate Derivative_n_imp_inc Derivative_n_imp_inc' Diffble_n_imp_inc:
  included.
*)

(* UNEXPORTED
Hint Resolve Deriv_lemma N_Deriv_lemma: derivate.
*)

(* UNEXPORTED
Hint Immediate Derivative_n_imp_Continuous Derivative_n_imp_Continuous':
  continuous.
*)

