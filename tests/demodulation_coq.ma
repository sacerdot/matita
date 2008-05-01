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

alias num = "Coq natural number".
alias symbol "times" = "Coq's natural times".
alias symbol "plus" = "Coq's natural plus".
alias symbol "eq" = "Coq's leibnitz's equality".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".

theorem p0 : \forall m:nat. m+O = m.
intro. demodulate.reflexivity.
qed.

theorem p: \forall m.1*m = m.
intros.demodulate.reflexivity.
qed.

theorem p2: \forall x,y:nat.(S x)*y = (y+x*y).
intros.demodulate.reflexivity.
qed.

theorem p1: \forall x,y:nat.(S ((S x)*y+x))=(S x)+(y*x+y).
intros.demodulate.reflexivity.
qed.

theorem p3: \forall x,y:nat. (x+y)*(x+y) = x*x + 2*(x*y) + (y*y).
intros.demodulate.reflexivity.
qed.

theorem p4: \forall x:nat. (x+1)*(x-1)=x*x - 1.
intro.
apply (nat_case x)
[simplify.reflexivity
|intro.demodulate.reflexivity]
qed.

