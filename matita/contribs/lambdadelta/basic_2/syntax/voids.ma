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

(* Basic inversion lemmas ***************************************************)

lemma voids_atom_inv: ∀K,n. ⓧ*[n]K = ⋆ → ∧∧ ⋆ = K & 0 = n.
#K * /2 width=1 by conj/
#n <voids_succ #H destruct
qed-.

lemma voids_pair_inv: ∀I,K1,K2,V,n. ⓧ*[n]K1 = K2.ⓑ{I}V →
                      ∧∧ K2.ⓑ{I}V = K1 & 0 = n.
#I #K1 #K2 #V * /2 width=1 by conj/
#n <voids_succ #H destruct
qed-.

(* Advanced inversion lemmas ************************************************)

lemma voids_inv_atom_sn: ∀n1,K2,n2. ⓧ*[n1]⋆ = ⓧ*[n2]K2 →
                         ∧∧ ⓧ*[n1-n2]⋆ = K2 & n2 ≤ n1.
#n1 elim n1 -n1
[ #K2 <voids_zero * /2 width=1 by conj/
  #n1 <voids_succ #H destruct
| #n1 #IH #K2 *
  [ <voids_zero #H destruct /2 width=1 by conj/
  | #n2 <voids_succ <voids_succ >minus_S_S #H
    elim (destruct_lbind_lbind_aux … H) -H #HK #_ (**) (* destruct lemma needed *)
    elim (IH … HK) -IH -HK #H #Hn destruct /3 width=1 by conj, le_S_S/
  ]
]
qed-.

lemma voids_inv_pair_sn: ∀I,V,n1,K1,K2,n2. ⓧ*[n1]K1.ⓑ{I}V = ⓧ*[n2]K2 →
                         ∧∧ ⓧ*[n1-n2]K1.ⓑ{I}V = K2 & n2 ≤ n1.
#I #V #n1 elim n1 -n1
[ #K1 #K2 <voids_zero * /2 width=1 by conj/
  #n1 <voids_succ #H destruct
| #n1 #IH #K1 #K2 *
  [ <voids_zero #H destruct /2 width=1 by conj/
  | #n2 <voids_succ <voids_succ >minus_S_S #H
    elim (destruct_lbind_lbind_aux … H) -H #HK #_ (**) (* destruct lemma needed *)
    elim (IH … HK) -IH -HK #H #Hn destruct /3 width=1 by conj, le_S_S/
  ]
]
qed-.

(* Main inversion properties ************************************************)

theorem voids_inj: ∀n. injective … (λL. ⓧ*[n]L).
#n elim n -n //
#n #IH #L1 #L2
<voids_succ <voids_succ #H
elim (destruct_lbind_lbind_aux … H) -H (**) (* destruct lemma needed *)
/2 width=1 by/
qed-.
