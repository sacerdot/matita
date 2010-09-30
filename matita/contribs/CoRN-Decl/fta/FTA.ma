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

set "baseuri" "cic:/matita/CoRN-Decl/fta/FTA".

include "CoRN.ma".

(* $Id: FTA.v,v 1.6 2004/04/23 10:00:57 lcf Exp $ *)

include "fta/CPoly_Rev.ma".

include "fta/FTAreg.ma".

(*#* * Fundamental Theorem of Algebra
%\begin{convention}% Let [n:nat] and [f] be a complex polynomial of
degree [(S n)].
%\end{convention}%
*)

(* UNEXPORTED
Section FTA_reg'
*)

alias id "f" = "cic:/CoRN/fta/FTA/FTA_reg'/f.var".

alias id "n" = "cic:/CoRN/fta/FTA/FTA_reg'/n.var".

alias id "f_degree" = "cic:/CoRN/fta/FTA/FTA_reg'/f_degree.var".

inline "cic:/CoRN/fta/FTA/FTA_reg'.con".

(* UNEXPORTED
End FTA_reg'
*)

(*#*
%\begin{convention}% Let [n:nat], [f] be a complex polynomial of degree
less than or equal to [(S n)] and [c] be a complex number such that
[f!c  [#]  Zero].
%\end{convention}%
*)

(* UNEXPORTED
Section FTA_1
*)

alias id "f" = "cic:/CoRN/fta/FTA/FTA_1/f.var".

alias id "n" = "cic:/CoRN/fta/FTA/FTA_1/n.var".

alias id "f_degree" = "cic:/CoRN/fta/FTA/FTA_1/f_degree.var".

alias id "c" = "cic:/CoRN/fta/FTA/FTA_1/c.var".

alias id "f_c" = "cic:/CoRN/fta/FTA/FTA_1/f_c.var".

inline "cic:/CoRN/fta/FTA/FTA_1a.con".

inline "cic:/CoRN/fta/FTA/FTA_1/g.con" "FTA_1__".

inline "cic:/CoRN/fta/FTA/FTA_1b.con".

inline "cic:/CoRN/fta/FTA/FTA_1.con".

inline "cic:/CoRN/fta/FTA/FTA_1'.con".

(* UNEXPORTED
End FTA_1
*)

(* UNEXPORTED
Section Fund_Thm_Alg
*)

inline "cic:/CoRN/fta/FTA/FTA'.con".

inline "cic:/CoRN/fta/FTA/FTA.con".

inline "cic:/CoRN/fta/FTA/FTA_a_la_Henk.con".

(* UNEXPORTED
End Fund_Thm_Alg
*)

