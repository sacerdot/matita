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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/Step".

include "CoRN.ma".

(* begin hide *)

(* UNEXPORTED
Declare ML Module "rational".
*)

(* UNEXPORTED
Ltac Algebra := auto with algebra_r algebra algebra_c algebra_s.
*)

(* UNEXPORTED
Ltac astepl x := stepl x; [idtac | Algebra].
*)

(* UNEXPORTED
Ltac astepr x := stepr x; [idtac | Algebra].
*)

(* UNEXPORTED
Tactic Notation "astepl" constr(c) :=  astepl c.
*)

(* UNEXPORTED
Tactic Notation "astepr" constr(c) :=  astepr c.
*)

(* UNEXPORTED
Ltac rstepl x := stepl x; [idtac | rational].
*)

(* UNEXPORTED
Ltac rstepr x := stepr x; [idtac | rational].
*)

(* UNEXPORTED
Tactic Notation "rstepl" constr(c) :=  rstepl c.
*)

(* UNEXPORTED
Tactic Notation "rstepr" constr(c) :=  rstepr c.
*)

(* UNEXPORTED
Ltac Included := eauto with included.
*)

(* end hide *)

(*#* * [algebra] and [step]
These tactics simplify equational reasoning.  See the references for a
description.

* [Included]
[Included] will solve goals of the form [(included A (dom F))].
*)

