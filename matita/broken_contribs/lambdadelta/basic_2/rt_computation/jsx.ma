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

include "ground/xoa/ex_4_3.ma".
include "basic_2/notation/relations/topredtysnstrong_3.ma".
include "basic_2/rt_computation/rsx.ma".

(* COMPATIBILITY OF STRONG NORMALIZATION FOR EXTENDED RT-TRANSITION *********)

(* Note: this should be an instance of a more general sex *)
(* Basic_2A1: uses: lcosx *)
inductive jsx (G): relation lenv ≝
| jsx_atom: jsx G (⋆) (⋆)
| jsx_bind: ∀I,K1,K2. jsx G K1 K2 →
            jsx G (K1.ⓘ[I]) (K2.ⓘ[I])
| jsx_pair: ∀I,K1,K2,V. jsx G K1 K2 →
            G ⊢ ⬈*𝐒[V] K2 → jsx G (K1.ⓑ[I]V) (K2.ⓧ)
.

interpretation
  "strong normalization for extended parallel rt-transition (compatibility)"
  'ToPRedTySNStrong G L1 L2 = (jsx G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact jsx_inv_atom_sn_aux (G):
     ∀L1,L2. G ⊢ L1 ⊒ L2 → L1 = ⋆ → L2 = ⋆.
#G #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #_ #H destruct
| #I #K1 #K2 #V #_ #_ #H destruct
]
qed-.

lemma jsx_inv_atom_sn (G):
      ∀L2. G ⊢ ⋆ ⊒ L2 → L2 = ⋆.
/2 width=5 by jsx_inv_atom_sn_aux/ qed-.

fact jsx_inv_bind_sn_aux (G):
     ∀L1,L2. G ⊢ L1 ⊒ L2 →
     ∀I,K1. L1 = K1.ⓘ[I] →
     ∨∨ ∃∃K2. G ⊢ K1 ⊒ K2 & L2 = K2.ⓘ[I]
      | ∃∃J,K2,V. G ⊢ K1 ⊒ K2 & G ⊢ ⬈*𝐒[V] K2 & I = BPair J V & L2 = K2.ⓧ.
#G #L1 #L2 * -L1 -L2
[ #J #L1 #H destruct
| #I #K1 #K2 #HK12 #J #L1 #H destruct /3 width=3 by ex2_intro, or_introl/
| #I #K1 #K2 #V #HK12 #HV #J #L1 #H destruct /3 width=7 by ex4_3_intro, or_intror/
]
qed-.

lemma jsx_inv_bind_sn (G):
      ∀I,K1,L2. G ⊢ K1.ⓘ[I] ⊒ L2 →
      ∨∨ ∃∃K2. G ⊢ K1 ⊒ K2 & L2 = K2.ⓘ[I]
       | ∃∃J,K2,V. G ⊢ K1 ⊒ K2 & G ⊢ ⬈*𝐒[V] K2 & I = BPair J V & L2 = K2.ⓧ.
/2 width=3 by jsx_inv_bind_sn_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: lcosx_inv_pair *)
lemma jsx_inv_pair_sn (G):
      ∀I,K1,L2,V. G ⊢ K1.ⓑ[I]V ⊒ L2 →
      ∨∨ ∃∃K2. G ⊢ K1 ⊒ K2 & L2 = K2.ⓑ[I]V
       | ∃∃K2. G ⊢ K1 ⊒ K2 & G ⊢ ⬈*𝐒[V] K2 & L2 = K2.ⓧ.
#G #I #K1 #L2 #V #H elim (jsx_inv_bind_sn … H) -H *
[ /3 width=3 by ex2_intro, or_introl/
| #J #K2 #X #HK12 #HX #H1 #H2 destruct /3 width=4 by ex3_intro, or_intror/
]
qed-.

lemma jsx_inv_void_sn (G):
      ∀K1,L2. G ⊢ K1.ⓧ ⊒ L2 →
      ∃∃K2. G ⊢ K1 ⊒ K2 & L2 = K2.ⓧ.
#G #K1 #L2 #H elim (jsx_inv_bind_sn … H) -H *
/2 width=3 by ex2_intro/
qed-.

(* Advanced forward lemmas **************************************************)

lemma jsx_fwd_bind_sn (G):
      ∀I1,K1,L2. G ⊢ K1.ⓘ[I1] ⊒ L2 →
      ∃∃I2,K2. G ⊢ K1 ⊒ K2 & L2 = K2.ⓘ[I2].
#G #I1 #K1 #L2 #H elim (jsx_inv_bind_sn … H) -H *
/2 width=4 by ex2_2_intro/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lcosx_O *)
lemma jsx_refl (G):
      reflexive … (jsx G).
#G #L elim L -L /2 width=1 by jsx_atom, jsx_bind/
qed.

(* Basic_2A1: removed theorems 2:
              lcosx_drop_trans_lt lcosx_inv_succ
*)
