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

set "baseuri" "cic:/matita/RELATIONAL/BEq/defs".

include "logic/equality.ma".

include "BNot/defs.ma".

inductive BEq (b1:Bool): Bool \to Bool \to Prop \def
   | beq_false: \forall b2. (~b1 == b2) \to BEq b1 false b2
   | beq_true : BEq b1 true b1
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "boolean coimplication predicate" 'rel_coimp x y z = 
   (cic:/matita/RELATIONAL/BEq/defs/BEq.ind#xpointer(1/1) x y z).

notation "hvbox(a break * b break == c)" 
  non associative with precedence 95
for @{ 'rel_coimp $a $b $c}.
