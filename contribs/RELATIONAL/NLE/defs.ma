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

set "baseuri" "cic:/matita/RELATIONAL/NLE/defs".

include "NPlus/defs.ma".

inductive NLE (q:Nat) (r:Nat): Prop \def
   | nle_nplus: \forall p. (p + q == r) \to NLE q r. 

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'less or equal to'" 'leq x y =
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) x y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'less than'" 'lt x y = 
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) 
      (cic:/matita/RELATIONAL/Nat/defs/Nat.ind#xpointer(1/1/2) x) y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'greater or equal to'" 'geq y x=
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) x y).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "natural 'greater than'" 'gt y x = 
   (cic:/matita/RELATIONAL/NLE/defs/NLE.ind#xpointer(1/1) 
      (cic:/matita/RELATIONAL/Nat/defs/Nat.ind#xpointer(1/1/2) x) y).
