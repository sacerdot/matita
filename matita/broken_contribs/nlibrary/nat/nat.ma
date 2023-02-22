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

include "hints_declaration.ma".
include "logic/equality.ma".
include "sets/setoids.ma".

ninductive nat: Type[0] ≝
   O: nat
 | S: nat → nat.

ndefinition NAT: setoid.
 napply mk_setoid [ napply nat | napply EQ]
nqed.

alias symbol "hint_decl" = "hint_decl_Type1".
unification hint 0 ≔ ⊢ carr NAT ≡ nat.
