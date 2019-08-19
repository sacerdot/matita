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

include "basic_2/notation/relations/lrsubeqv_5.ma".
include "basic_2/dynamic/cnv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

inductive lsubv (a) (h) (G): relation lenv ≝
| lsubv_atom: lsubv a h G (⋆) (⋆)
| lsubv_bind: ∀I,L1,L2. lsubv a h G L1 L2 → lsubv a h G (L1.ⓘ{I}) (L2.ⓘ{I})
| lsubv_beta: ∀L1,L2,W,V. ⦃G,L1⦄ ⊢ ⓝW.V ![a,h] →
              lsubv a h G L1 L2 → lsubv a h G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (native validity)"
  'LRSubEqV a h G L1 L2 = (lsubv a h G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubv_inv_atom_sn_aux (a) (h) (G):
     ∀L1,L2. G ⊢ L1 ⫃![a,h] L2 → L1 = ⋆ → L2 = ⋆.
#a #h #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #W #V #_ #_ #H destruct
]
qed-.

(* Basic_2A1: uses: lsubsv_inv_atom1 *)
lemma lsubv_inv_atom_sn (a) (h) (G):
      ∀L2. G ⊢ ⋆ ⫃![a,h] L2 → L2 = ⋆.
/2 width=6 by lsubv_inv_atom_sn_aux/ qed-.

fact lsubv_inv_bind_sn_aux (a) (h) (G): ∀L1,L2. G ⊢ L1 ⫃![a,h] L2 →
     ∀I,K1. L1 = K1.ⓘ{I} →
     ∨∨ ∃∃K2. G ⊢ K1 ⫃![a,h] K2 & L2 = K2.ⓘ{I}
      | ∃∃K2,W,V. ⦃G,K1⦄ ⊢ ⓝW.V ![a,h] & G ⊢ K1 ⫃![a,h] K2
                & I = BPair Abbr (ⓝW.V) & L2 = K2.ⓛW.
#a #h #G #L1 #L2 * -L1 -L2
[ #J #K1 #H destruct
| #I #L1 #L2 #HL12 #J #K1 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #HWV #HL12 #J #K1 #H destruct /3 width=7 by ex4_3_intro, or_intror/
]
qed-.

(* Basic_2A1: uses: lsubsv_inv_pair1 *)
lemma lsubv_inv_bind_sn (a) (h) (G):
      ∀I,K1,L2. G ⊢ K1.ⓘ{I} ⫃![a,h] L2 →
      ∨∨ ∃∃K2. G ⊢ K1 ⫃![a,h] K2 & L2 = K2.ⓘ{I}
       | ∃∃K2,W,V. ⦃G,K1⦄ ⊢ ⓝW.V ![a,h] & G ⊢ K1 ⫃![a,h] K2
                 & I = BPair Abbr (ⓝW.V) & L2 = K2.ⓛW.
/2 width=3 by lsubv_inv_bind_sn_aux/ qed-.

fact lsubv_inv_atom_dx_aux (a) (h) (G):
     ∀L1,L2. G ⊢ L1 ⫃![a,h] L2 → L2 = ⋆ → L1 = ⋆.
#a #h #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #_ #H destruct
| #L1 #L2 #W #V #_ #_ #H destruct
]
qed-.

(* Basic_2A1: uses: lsubsv_inv_atom2 *)
lemma lsubv_inv_atom2 (a) (h) (G):
      ∀L1. G ⊢ L1 ⫃![a,h] ⋆ → L1 = ⋆.
/2 width=6 by lsubv_inv_atom_dx_aux/ qed-.

fact lsubv_inv_bind_dx_aux (a) (h) (G):
     ∀L1,L2. G ⊢ L1 ⫃![a,h] L2 →
     ∀I,K2. L2 = K2.ⓘ{I} →
     ∨∨ ∃∃K1. G ⊢ K1 ⫃![a,h] K2 & L1 = K1.ⓘ{I}
      | ∃∃K1,W,V. ⦃G,K1⦄ ⊢ ⓝW.V ![a,h] &
                  G ⊢ K1 ⫃![a,h] K2 & I = BPair Abst W & L1 = K1.ⓓⓝW.V.
#a #h #G #L1 #L2 * -L1 -L2
[ #J #K2 #H destruct
| #I #L1 #L2 #HL12 #J #K2 #H destruct /3 width=3 by ex2_intro, or_introl/
| #L1 #L2 #W #V #HWV #HL12 #J #K2 #H destruct /3 width=7 by ex4_3_intro, or_intror/
]
qed-.

(* Basic_2A1: uses: lsubsv_inv_pair2 *)
lemma lsubv_inv_bind_dx (a) (h) (G):
      ∀I,L1,K2. G ⊢ L1 ⫃![a,h] K2.ⓘ{I} →
      ∨∨ ∃∃K1. G ⊢ K1 ⫃![a,h] K2 & L1 = K1.ⓘ{I}
       | ∃∃K1,W,V. ⦃G,K1⦄ ⊢ ⓝW.V ![a,h] &
                   G ⊢ K1 ⫃![a,h] K2 & I = BPair Abst W & L1 = K1.ⓓⓝW.V.
/2 width=3 by lsubv_inv_bind_dx_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsubv_inv_abst_sn (a) (h) (G):
      ∀K1,L2,W. G ⊢ K1.ⓛW ⫃![a,h] L2 →
      ∃∃K2. G ⊢ K1 ⫃![a,h] K2 & L2 = K2.ⓛW.
#a #h #G #K1 #L2 #W #H
elim (lsubv_inv_bind_sn … H) -H // *
#K2 #XW #XV #_ #_ #H1 #H2 destruct
qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: uses: lsubsv_refl *)
lemma lsubv_refl (a) (h) (G): reflexive … (lsubv a h G).
#a #h #G #L elim L -L /2 width=1 by lsubv_atom, lsubv_bind/
qed.

(* Basic_2A1: removed theorems 3:
              lsubsv_lstas_trans lsubsv_sta_trans
              lsubsv_fwd_lsubd
*)
