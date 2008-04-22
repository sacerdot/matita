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



include "nat/minus.ma".

theorem p2: \forall x,y:nat. x+x = (S(S O))*x.
intros.
demodulate by times_n_Sm times_n_O sym_times plus_n_O.
qed.

theorem p4: \forall x:nat. (x+(S O))*(x-(S O))=x*x - (S O).
intro.
apply (nat_case x)
[simplify.reflexivity
|intro.demodulate.reflexivity]
qed.

theorem p5: \forall x,y:nat. (x+y)*(x+y) = x*x + (S(S O))*(x*y) + (y*y).
intros.demodulate.reflexivity.
qed.

