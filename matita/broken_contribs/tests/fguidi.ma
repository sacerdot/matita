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

include "logic/connectives.ma".
include "nat/nat.ma".

theorem eq_S_S: \forall m,n. m = n \to (S m) = (S n).
intros; destruct; autobatch.
qed.

inductive le: nat \to nat \to Prop \def
     le_zero: \forall n. (le O n)
   | le_succ: \forall m, n. (le m n) \to (le (S m) (S n)).

theorem le_refl: \forall x. (le x x).
intros; elim x; clear x; autobatch.
qed.

theorem le_gen_x_O_aux: \forall x, y. (le x y) \to (y =O) \to (x = O).
intros 3; elim H; clear H x y;
[ autobatch
| destruct
]
qed.

theorem le_gen_x_O: \forall x. (le x O) \to (x = O).
intros; lapply linear le_gen_x_O_aux to H;
[ destruct; autobatch
| autobatch
].
qed.

theorem le_x_O: \forall x. (x = O) \to (le x O).
intros; destruct; autobatch.
qed.

theorem le_gen_S_x_aux: \forall m,x,y. (le y x) \to (y = S m) \to 
                        (\exists n. x = (S n) \land (le m n)).
intros 4; elim H; clear H x y;
[ destruct
| destruct; autobatch
].
qed.

theorem le_gen_S_x: \forall m,x. (le (S m) x) \to 
                    (\exists n. x = (S n) \land (le m n)).
intros; lapply le_gen_S_x_aux to H; autobatch.
qed.

theorem le_S_x: \forall m,x. (\exists n. x = (S n) \land (le m n)) \to
                (le (S m) x).
intros; decompose; destruct; autobatch.
qed.

theorem le_gen_S_S: \forall m,n. (le (S m) (S n)) \to (le m n).
intros.
lapply linear le_gen_S_x to H as H0; decompose; destruct; autobatch.
qed.

theorem le_S_S: \forall m,n. (le m n) \to (le (S m) (S n)).
intros; autobatch.
qed.

theorem le_trans: \forall x,y. (le x y) \to \forall z. (le y z) \to (le x z).
intros 3. elim H; clear H x y;
[ autobatch
| lapply linear le_gen_S_x to H3; decompose; destruct; autobatch.
].
qed.
