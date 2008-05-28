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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CSetoidInc".

include "CoRN.ma".

(* $Id: CSetoidInc.v,v 1.3 2004/04/22 14:49:43 lcf Exp $ *)

(*#* printing included %\ensuremath{\subseteq}% #&sube;# *)

include "algebra/CSetoidFun.ma".

(* UNEXPORTED
Section inclusion
*)

(*#* ** Inclusion

Let [S] be a setoid, and [P], [Q], [R] be predicates on [S]. *)

alias id "S" = "cic:/CoRN/algebra/CSetoidInc/inclusion/S.var".

inline "cic:/CoRN/algebra/CSetoidInc/included.con".

(* UNEXPORTED
Section Basics
*)

alias id "P" = "cic:/CoRN/algebra/CSetoidInc/inclusion/Basics/P.var".

alias id "Q" = "cic:/CoRN/algebra/CSetoidInc/inclusion/Basics/Q.var".

alias id "R" = "cic:/CoRN/algebra/CSetoidInc/inclusion/Basics/R.var".

inline "cic:/CoRN/algebra/CSetoidInc/included_refl.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_trans.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_conj.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_conj'.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_conj''.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_conj_lft.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_conj_rht.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_extend.con".

(* UNEXPORTED
End Basics
*)

(*#*
%\begin{convention}% Let [I,R:S->CProp] and [F G:(PartFunct S)], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CSetoidInc/inclusion/F.var".

alias id "G" = "cic:/CoRN/algebra/CSetoidInc/inclusion/G.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CSetoidInc/inclusion/P.con" "inclusion__".

inline "cic:/CoRN/algebra/CSetoidInc/inclusion/Q.con" "inclusion__".

(* end hide *)

alias id "R" = "cic:/CoRN/algebra/CSetoidInc/inclusion/R.var".

inline "cic:/CoRN/algebra/CSetoidInc/included_FComp.con".

inline "cic:/CoRN/algebra/CSetoidInc/included_FComp'.con".

(* UNEXPORTED
End inclusion
*)

(* UNEXPORTED
Implicit Arguments included [S].
*)

(* UNEXPORTED
Hint Resolve included_refl included_FComp : included.
*)

(* UNEXPORTED
Hint Immediate included_trans included_FComp' : included.
*)

