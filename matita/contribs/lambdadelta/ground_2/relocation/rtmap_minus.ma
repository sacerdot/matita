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

include "ground_2/relocation/rtmap_tl.ma".

(* RELOCATION MAP ***********************************************************)

let rec minus (f:rtmap) (n:nat) on n: rtmap ≝ match n with
[ O ⇒ f | S m ⇒ ↓(minus f m) ].

interpretation "minus (rtmap)" 'minus f n = (minus f n).

(* Basic properties *********************************************************)

lemma minus_rew_O: ∀f. f = f - 0.
// qed.

lemma minus_rew_S: ∀f,n. ↓(f - n) = f - ⫯n.
// qed.

lemma minus_eq_repl: ∀n. eq_repl (λf1,f2. f1 - n ≗ f2 - n).
#n elim n -n /3 width=1 by tl_eq_repl/
qed.

(* Advancedd properties *****************************************************)

lemma minus_xn: ∀n,f. (↓f) - n = f - ⫯n.
#n elim n -n //
qed.
