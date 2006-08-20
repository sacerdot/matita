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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICS/NPlus".

include "logic/equality.ma".

include "Nat.ma".

inductive NPlus (p:Nat): Nat \to Nat \to Prop \def
   | NPlus_zero_2: NPlus p zero p
   | NPlus_succ_2: \forall q, r. NPlus p q r \to NPlus p (succ q) (succ r).
