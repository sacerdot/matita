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

include "ground/notation/functions/droppreds_2.ma".
include "ground/relocation/rtmap_pushs.ma".
include "ground/relocation/rtmap_tl.ma".

(* RELOCATION MAP ***********************************************************)

rec definition tls (f:rtmap) (n:nat) on n: rtmap ≝ match n with
[ O ⇒ f | S m ⇒ ⫱(tls f m) ].

interpretation "tls (rtmap)" 'DropPreds n f = (tls f n).

(* Basic properties *********************************************************)

lemma tls_O: ∀f. f = ⫱*[0] f.
// qed.

lemma tls_S: ∀f,n. ⫱ ⫱*[n] f = ⫱*[↑n] f.
// qed.

lemma tls_eq_repl: ∀n. eq_repl (λf1,f2. ⫱*[n] f1 ≡ ⫱*[n] f2).
#n elim n -n /3 width=1 by tl_eq_repl/
qed.

(* Advanced properties ******************************************************)

lemma tls_xn: ∀n,f. ⫱*[n] ⫱f = ⫱*[↑n] f.
#n elim n -n //
qed.

(* Properties with pushs ****************************************************)

lemma tls_pushs: ∀n,f. f = ⫱*[n] ⫯*[n] f.
#n elim n -n //
#n #IH #f <tls_xn //
qed.
