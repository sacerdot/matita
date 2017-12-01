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

include "basic_2/notation/relations/rvoidstar_4.ma".
include "basic_2/syntax/lenv.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

inductive voids: bi_relation nat lenv ≝
| voids_atom   : voids 0 (⋆) 0 (⋆)
| voids_pair_sn: ∀I1,I2,K1,K2,V1,n. voids n K1 n K2 →
                 voids 0 (K1.ⓑ{I1}V1) 0 (K2.ⓘ{I2})
| voids_pair_dx: ∀I1,I2,K1,K2,V2,n. voids n K1 n K2 →
                 voids 0 (K1.ⓘ{I1}) 0 (K2.ⓑ{I2}V2)
| voids_void_sn: ∀K1,K2,n1,n2. voids n1 K1 n2 K2 →
                 voids (⫯n1) (K1.ⓧ) n2 K2
| voids_void_dx: ∀K1,K2,n1,n2. voids n1 K1 n2 K2 →
                 voids n1 K1 (⫯n2) (K2.ⓧ)
.

interpretation "equivalence up to exclusion binders (local environment)"
   'RVoidStar n1 L1 n2 L2 = (voids n1 L1 n2 L2).

(* Basic properties *********************************************************)

lemma voids_refl: ∀L. ∃n. ⓧ*[n]L ≋ ⓧ*[n]L.
#L elim L -L /2 width=2 by ex_intro, voids_atom/
#L #I * #n #IH cases I -I /3 width=2 by ex_intro, voids_pair_dx/
* /4 width=2 by ex_intro, voids_void_sn, voids_void_dx/
qed-.

lemma voids_sym: bi_symmetric … voids.
#n1 #n2 #L1 #L2 #H elim H -L1 -L2 -n1 -n2
/2 width=2 by voids_atom, voids_pair_sn, voids_pair_dx, voids_void_sn, voids_void_dx/
qed-.

(*




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
*)