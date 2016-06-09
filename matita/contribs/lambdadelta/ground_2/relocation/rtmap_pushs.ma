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

include "ground_2/notation/functions/liftstar_2.ma".
include "ground_2/relocation/rtmap_eq.ma".

(* RELOCATION MAP ***********************************************************)

rec definition pushs (f:rtmap) (n:nat) on n: rtmap ≝ match n with
[ O ⇒ f | S m ⇒ ↑(pushs f m) ].

interpretation "pushs (rtmap)" 'LiftStar n f = (pushs f n).

(* Basic properties *********************************************************)

lemma pushs_O: ∀f. f = ↑*[0] f.
// qed.

lemma pushs_S: ∀f,n. ↑↑*[n] f = ↑*[⫯n] f.
// qed.

lemma pushs_eq_repl: ∀n. eq_repl (λf1,f2. ↑*[n] f1 ≗ ↑*[n] f2).
#n elim n -n /3 width=5 by eq_push/
qed.

(* Advanced properties ******************************************************)

lemma pushs_xn: ∀n,f. ↑*[n] ↑f = ↑*[⫯n] f.
#n elim n -n //
qed.
