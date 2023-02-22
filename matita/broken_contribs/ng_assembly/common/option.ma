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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/bool.ma".

(* ****** *)
(* OPTION *)
(* ****** *)

ninductive option (A:Type) : Type ≝
  None : option A
| Some : A → option A.

ndefinition eq_option ≝
λT.λf:T → T → bool.λop1,op2:option T.
 match op1 with
  [ None ⇒ match op2 with [ None ⇒ true | Some _ ⇒ false ]
  | Some x1 ⇒ match op2 with [ None ⇒ false | Some x2 ⇒ f x1 x2 ]
  ].

(* option map = match ... with [ None ⇒ None ? | Some .. ⇒ .. ] *)
ndefinition opt_map ≝
λT1,T2:Type.λt:option T1.λf:T1 → option T2.
 match t with [ None ⇒ None ? | Some x ⇒ (f x) ].
