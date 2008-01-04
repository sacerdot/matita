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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/ListType".

include "CoRN.ma".

(* begin hide *)

(*#**********************************************************************)

(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)

(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)

(*   \VV/  *************************************************************)

(*    //   *      This file is distributed under the terms of the      *)

(*         *       GNU Lesser General Public License Version 2.1       *)

(*#**********************************************************************)

(*i $Id: ListType.v,v 1.2 2004/03/26 16:07:02 lcf Exp $ i*)

(* THIS IS A OLD CONTRIB. IT IS NO LONGER MAINTAINED ***)

(* Moved to Type for CoRN *)

(* end hide *)

(*#*
%\cleardoublepage\setcounter{page}{1}%
*Lists in Type

This file contains a variant of the development of lists in the standard
library of Coq but moved to the Type level.
*)

(* UNEXPORTED
Section List
*)

alias id "A" = "cic:/CoRN/algebra/ListType/List/A.var".

inline "cic:/CoRN/algebra/ListType/list.ind".

inline "cic:/CoRN/algebra/ListType/app.con".

inline "cic:/CoRN/algebra/ListType/app_nil_end.con".

(* UNEXPORTED
Hint Resolve app_nil_end: list v62.
*)

inline "cic:/CoRN/algebra/ListType/app_ass.con".

(* UNEXPORTED
Hint Resolve app_ass: list v62.
*)

inline "cic:/CoRN/algebra/ListType/ass_app.con".

(* UNEXPORTED
Hint Resolve ass_app: list v62.
*)

inline "cic:/CoRN/algebra/ListType/tail.con".

inline "cic:/CoRN/algebra/ListType/nil_cons.con".

(*#***************************************)

(* Length of lists                      *)

(*#***************************************)

inline "cic:/CoRN/algebra/ListType/length.con".

(*#*****************************)

(* Length order of lists      *)

(*#*****************************)

(* UNEXPORTED
Section length_order
*)

inline "cic:/CoRN/algebra/ListType/lel.con".

(* UNEXPORTED
Hint Unfold lel: list.
*)

alias id "a" = "cic:/CoRN/algebra/ListType/List/length_order/a.var".

alias id "b" = "cic:/CoRN/algebra/ListType/List/length_order/b.var".

alias id "l" = "cic:/CoRN/algebra/ListType/List/length_order/l.var".

alias id "m" = "cic:/CoRN/algebra/ListType/List/length_order/m.var".

alias id "n" = "cic:/CoRN/algebra/ListType/List/length_order/n.var".

inline "cic:/CoRN/algebra/ListType/lel_refl.con".

inline "cic:/CoRN/algebra/ListType/lel_trans.con".

inline "cic:/CoRN/algebra/ListType/lel_cons_cons.con".

inline "cic:/CoRN/algebra/ListType/lel_cons.con".

inline "cic:/CoRN/algebra/ListType/lel_tail.con".

inline "cic:/CoRN/algebra/ListType/lel_nil.con".

(* UNEXPORTED
End length_order
*)

(* UNEXPORTED
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons: list
  v62.
*)

inline "cic:/CoRN/algebra/ListType/In.con".

inline "cic:/CoRN/algebra/ListType/in_eq.con".

(* UNEXPORTED
Hint Resolve in_eq: list v62.
*)

inline "cic:/CoRN/algebra/ListType/in_cons.con".

(* UNEXPORTED
Hint Resolve in_cons: list v62.
*)

inline "cic:/CoRN/algebra/ListType/in_app_or.con".

(* UNEXPORTED
Hint Immediate in_app_or: list v62.
*)

inline "cic:/CoRN/algebra/ListType/in_or_app.con".

(* UNEXPORTED
Hint Resolve in_or_app: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl.con".

(* UNEXPORTED
Hint Unfold incl: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_refl.con".

(* UNEXPORTED
Hint Resolve incl_refl: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_tl.con".

(* UNEXPORTED
Hint Immediate incl_tl: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_tran.con".

inline "cic:/CoRN/algebra/ListType/incl_appl.con".

(* UNEXPORTED
Hint Immediate incl_appl: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_appr.con".

(* UNEXPORTED
Hint Immediate incl_appr: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_cons.con".

(* UNEXPORTED
Hint Resolve incl_cons: list v62.
*)

inline "cic:/CoRN/algebra/ListType/incl_app.con".

(* UNEXPORTED
End List
*)

(* UNEXPORTED
Implicit Arguments length [A].
*)

(* UNEXPORTED
Implicit Arguments In [A].
*)

(* UNEXPORTED
Implicit Arguments cons [A].
*)

(* UNEXPORTED
Section Map
*)

alias id "A" = "cic:/CoRN/algebra/ListType/Map/A.var".

alias id "B" = "cic:/CoRN/algebra/ListType/Map/B.var".

alias id "f" = "cic:/CoRN/algebra/ListType/Map/f.var".

inline "cic:/CoRN/algebra/ListType/map.con".

(* UNEXPORTED
End Map
*)

(* UNEXPORTED
Implicit Arguments map [A B].
*)

(* UNEXPORTED
Hint Resolve incl_app: list v62.
*)

