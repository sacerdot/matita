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



include "NPlus/defs.ma".

inductive NLE: Nat \to Nat \to Prop \def
   | nle_zero_1: \forall q. NLE zero q
   | nle_succ_succ: \forall p,q. NLE p q \to NLE (succ p) (succ q)
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'greater or equal to'" 'geq y x=
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) x y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'greater than'" 'gt y x = 
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) 
      (cic:/matita/RELATIONAL/datatypes/Nat/Nat.ind#xpointer(1/1/2) x) y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'less or equal to'" 'leq x y =
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) x y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'less than'" 'lt x y = 
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) 
      (cic:/matita/RELATIONAL/datatypes/Nat/Nat.ind#xpointer(1/1/2) x) y).
