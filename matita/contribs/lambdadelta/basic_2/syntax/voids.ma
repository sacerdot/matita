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

include "basic_2/notation/functions/voidstar_2.ma".
include "basic_2/syntax/lenv.ma".

(* EXTENSION OF A LOCAL ENVIRONMENT WITH EXCLUSION BINDERS ******************)

rec definition voids (L:lenv) (n:nat) on n: lenv ≝ match n with
[ O ⇒ L | S m ⇒ (voids L m).ⓧ ].

interpretation "extension with exclusion binders (local environment)"
   'VoidStar n L = (voids L n).

(* Basic properties *********************************************************)

lemma voids_zero: ∀L. L = ⓧ*[0]L.
// qed.

lemma voids_succ: ∀L,n. (ⓧ*[n]L).ⓧ = ⓧ*[⫯n]L.
// qed.

(* Advanced properties ******************************************************)

lemma voids_next: ∀n,L. ⓧ*[n](L.ⓧ) = ⓧ*[⫯n]L.
#n elim n -n //
qed.

(* Main inversion properties ************************************************)

theorem voids_inj: ∀n. injective … (λL. ⓧ*[n]L).
#n elim n -n //
#n #IH #L1 #L2
<voids_succ <voids_succ #H
elim (destruct_lbind_lbind_aux … H) -H (**) (* destruct lemma needed *)
/2 width=1 by/
qed-.
