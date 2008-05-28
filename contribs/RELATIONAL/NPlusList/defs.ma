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



include "datatypes/List.ma".
include "NPlus/defs.ma".


inductive NPlusList: (List Nat) \to Nat \to Prop \def
   | nplus_nil: NPlusList (nil ?) zero  
   | nplus_cons: \forall l,p,q,r. 
                 NPlusList l p \to NPlus p q r \to NPlusList (cons ? l q) r
.

definition NPlusListEq: (List Nat) \to (List Nat) \to Prop \def
   \lambda ns1,ns2. \exists n. NPlusList ns1 n \land NPlusList ns2 n.

(*
(*CSC: the URI must disappear: there is a bug now *)
interpretation "ternary natural plus predicate" 'rel_plus3 x y z = 
   (cic:/matita/RELATIONAL/NPlus/defs/NPlus3.con w x y z).

notation "hvbox(a break + b break + c == d)" 
  non associative with precedence 95
for @{ 'rel_plus3 $a $b $c $d}.
*)
