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




alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".

let rec plus n m \def
 match n with
  [ O \Rightarrow m
  | (S x) \Rightarrow S (plus x m) ].
