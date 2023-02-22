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


include "coq.ma".

alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "n" = "cic:/Suresnes/BDD/canonicite/Canonicity_BDT/n.con".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
theorem a: 
  (\forall p: nat \to Prop.
  \forall n: nat. p n \to p n ) \to (eq nat n n).
intro.
apply (H (\lambda n:nat.(eq nat n n))).
reflexivity.
qed.
