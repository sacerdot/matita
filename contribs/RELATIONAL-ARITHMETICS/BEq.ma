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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICS/BEq".

include "logic/equality.ma".

include "BNot.ma".

inductive BEq (b1:Bool): Bool \to Bool \to Prop \def
   | BEq_false: \forall b2. BNot b1 b2 \to BEq b1 false b2
   | BEq_true : BEq b1 true b1.
