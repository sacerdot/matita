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



include "preamble.ma".

inductive List (A: Type): Type \def
   | nil: List A
   | cons: List A \to A \to List A
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "nil" 'nil = 
   (cic:/matita/RELATIONAL/datatypes/List/List.ind#xpointer(1/1) ?).

notation "hvbox([])"
  non associative with precedence 95
for @{ 'nil }.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "right cons" 'rcons x y = 
   (cic:/matita/RELATIONAL/datatypes/List/List.ind#xpointer(1/2) ? x y).

notation "hvbox([a break @ b])"
  non associative with precedence 95
for @{ 'rcons $a $b}.

