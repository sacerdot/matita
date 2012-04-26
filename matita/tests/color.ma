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

notation < "mstyle mathsize big color #ff0000 background #0000ff scriptsizemultiplier 0.8 (x)" 
 non associative with precedence 55 for @{'red $x}.

definition red : ∀X:Type.∀t:X.X ≝ λT.λt.t.
interpretation "red" 'red x = (red _ x).

include "logic/equality.ma".
include "nat/nat.ma".
alias num (instance 0) = "natural number".
lemma foo : red ? 3 = 3.
reflexivity.
qed.