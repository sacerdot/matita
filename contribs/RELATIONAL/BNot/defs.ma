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

set "baseuri" "cic:/matita/RELATIONAL/BNot/defs".

include "logic/equality.ma".

include "Bool/defs.ma".

inductive BNot: Bool \to Bool \to Prop \def
   | bnot_false: BNot false true
   | bnot_true : BNot true false
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "boolean not predicate" 'rel_not x y = 
   (cic:/matita/RELATIONAL/BNot/defs/BNot.ind#xpointer(1/1) x y).

(* FG: we can not use - here for some reason *)
notation "hvbox(~ a break == b)" 
  non associative with precedence 95
for @{ 'rel_not $a $b}.
