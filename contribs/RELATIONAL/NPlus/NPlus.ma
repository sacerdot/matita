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

set "baseuri" "cic:/matita/RELATIONAL/NPlus/defs".

include "logic/equality.ma".

include "Nat/Nat.ma".

inductive NPlus (p:Nat): Nat \to Nat \to Prop \def
   | nplus_zero_2: NPlus p zero p
   | nplus_succ_2: \forall q, r. NPlus p q r \to NPlus p (succ q) (succ r).
