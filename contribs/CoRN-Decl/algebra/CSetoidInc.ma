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

(* $Id: CSetoidInc.v,v 1.3 2004/04/22 14:49:43 lcf Exp $ *)

(*#* printing included %\ensuremath{\subseteq}% #&sube;# *)

(* INCLUDE
CSetoidFun
*)

(* UNEXPORTED
Section inclusion.
*)

(*#* ** Inclusion

Let [S] be a setoid, and [P], [Q], [R] be predicates on [S]. *)

inline cic:/CoRN/algebra/CSetoidInc/S.var.

inline cic:/CoRN/algebra/CSetoidInc/included.con.

(* UNEXPORTED
Section Basics.
*)

inline cic:/CoRN/algebra/CSetoidInc/P.var.

inline cic:/CoRN/algebra/CSetoidInc/Q.var.

inline cic:/CoRN/algebra/CSetoidInc/R.var.

inline cic:/CoRN/algebra/CSetoidInc/included_refl.con.

inline cic:/CoRN/algebra/CSetoidInc/included_trans.con.

inline cic:/CoRN/algebra/CSetoidInc/included_conj.con.

inline cic:/CoRN/algebra/CSetoidInc/included_conj'.con.

inline cic:/CoRN/algebra/CSetoidInc/included_conj''.con.

inline cic:/CoRN/algebra/CSetoidInc/included_conj_lft.con.

inline cic:/CoRN/algebra/CSetoidInc/included_conj_rht.con.

inline cic:/CoRN/algebra/CSetoidInc/included_extend.con.

(* UNEXPORTED
End Basics.
*)

(*#*
%\begin{convention}% Let [I,R:S->CProp] and [F G:(PartFunct S)], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

inline cic:/CoRN/algebra/CSetoidInc/F.var.

inline cic:/CoRN/algebra/CSetoidInc/G.var.

(* begin hide *)

inline cic:/CoRN/algebra/CSetoidInc/P.con.

inline cic:/CoRN/algebra/CSetoidInc/Q.con.

(* end hide *)

inline cic:/CoRN/algebra/CSetoidInc/R.var.

inline cic:/CoRN/algebra/CSetoidInc/included_FComp.con.

inline cic:/CoRN/algebra/CSetoidInc/included_FComp'.con.

(* UNEXPORTED
End inclusion.
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

