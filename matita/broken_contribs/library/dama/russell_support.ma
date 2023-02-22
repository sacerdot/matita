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

include "nat/nat.ma".
include "logic/cprop_connectives.ma".

definition hide ≝ λT:Type.λx:T.x.

notation < "\blacksquare" non associative with precedence 55 for @{'hide}.
interpretation "hide" 'hide = (hide ? ?).
interpretation "hide2" 'hide = (hide ? ? ?).

definition inject ≝ λP.λa:nat.λp:P a. ex_introT ? P ? p.
coercion inject 0 1.
definition eject ≝ λP.λc: ∃n:nat.P n. match c with [ ex_introT w _ ⇒ w].
coercion eject.
