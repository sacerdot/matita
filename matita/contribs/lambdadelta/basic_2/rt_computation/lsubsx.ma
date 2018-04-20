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

include "basic_2/notation/relations/lsubeqx_6.ma".
include "basic_2/rt_computation/lfsx.ma".

(* CLEAR OF STRONGLY NORMALIZING ENTRIES FOR UNCOUNTED RT-TRANSITION ********)

(* Note: this should be an instance of a more general lexs *)
(* Basic_2A1: uses: lcosx *)
inductive lsubsx (h) (o) (G): rtmap → relation lenv ≝
| lsubsx_atom: ∀f. lsubsx h o G f (⋆) (⋆)
| lsubsx_push: ∀f,I,K1,K2. lsubsx h o G f K1 K2 →
               lsubsx h o G (⫯f) (K1.ⓘ{I}) (K2.ⓘ{I})
| lsubsx_unit: ∀f,I,K1,K2. lsubsx h o G f K1 K2 →
               lsubsx h o G (↑f) (K1.ⓤ{I}) (K2.ⓧ)
| lsubsx_pair: ∀f,I,K1,K2,V. G ⊢ ⬈*[h, o, V] 𝐒⦃K2⦄ →
               lsubsx h o G f K1 K2 → lsubsx h o G (↑f) (K1.ⓑ{I}V) (K2.ⓧ)
.

interpretation
  "local environment refinement (clear)"
  'LSubEqX h o f G L1 L2 = (lsubsx h o G f L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubsx_inv_atom_sn_aux: ∀h,o,g,G,L1,L2. G ⊢ L1 ⊆ⓧ[h, o, g] L2 →
                             L1 = ⋆ → L2 = ⋆.
#h #o #g #G #L1 #L2 * -g -L1 -L2 //
[ #f #I #K1 #K2 #_ #H destruct
| #f #I #K1 #K2 #_ #H destruct
| #f #I #K1 #K2 #V #_ #_ #H destruct
]
qed-.

lemma lsubsx_inv_atom_sn: ∀h,o,g,G,L2. G ⊢ ⋆ ⊆ⓧ[h, o, g] L2 → L2 = ⋆.
/2 width=7 by lsubsx_inv_atom_sn_aux/ qed-.

fact lsubsx_inv_push_sn_aux: ∀h,o,g,G,L1,L2. G ⊢ L1 ⊆ⓧ[h, o, g] L2 →
                             ∀f,I,K1. g = ⫯f → L1 = K1.ⓘ{I} →
                             ∃∃K2. G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓘ{I}.
#h #o #g #G #L1 #L2 * -g -L1 -L2
[ #f #g #J #L1 #_ #H destruct
| #f #I #K1 #K2 #HK12 #g #J #L1 #H1 #H2 destruct
  <(injective_push … H1) -g /2 width=3 by ex2_intro/
| #f #I #K1 #K2 #_ #g #J #L1 #H
  elim (discr_next_push … H)
| #f #I #K1 #K2 #V #_ #_ #g #J #L1 #H
  elim (discr_next_push … H)
]
qed-.

lemma lsubsx_inv_push_sn: ∀h,o,f,I,G,K1,L2. G ⊢ K1.ⓘ{I} ⊆ⓧ[h, o, ⫯f] L2 →
                          ∃∃K2. G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓘ{I}.
/2 width=5 by lsubsx_inv_push_sn_aux/ qed-.

fact lsubsx_inv_unit_sn_aux: ∀h,o,g,G,L1,L2. G ⊢ L1 ⊆ⓧ[h, o, g] L2 →
                             ∀f,I,K1. g = ↑f → L1 = K1.ⓤ{I} →
                             ∃∃K2. G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓧ.
#h #o #g #G #L1 #L2 * -g -L1 -L2
[ #f #g #J #L1 #_ #H destruct
| #f #I #K1 #K2 #_ #g #J #L1 #H
  elim (discr_push_next … H)
| #f #I #K1 #K2 #HK12 #g #J #L1 #H1 #H2 destruct
  <(injective_next … H1) -g /2 width=3 by ex2_intro/
| #f #I #K1 #K2 #V #_ #_ #g #J #L1 #_ #H destruct
]
qed-.

lemma lsubsx_inv_unit_sn: ∀h,o,f,I,G,K1,L2. G ⊢ K1.ⓤ{I} ⊆ⓧ[h, o, ↑f] L2 →
                          ∃∃K2. G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓧ.
/2 width=6 by lsubsx_inv_unit_sn_aux/ qed-.

fact lsubsx_inv_pair_sn_aux: ∀h,o,g,G,L1,L2. G ⊢ L1 ⊆ⓧ[h, o, g] L2 →
                             ∀f,I,K1,V. g = ↑f → L1 = K1.ⓑ{I}V →
                             ∃∃K2. G ⊢ ⬈*[h, o, V] 𝐒⦃K2⦄ &
                                   G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓧ.
#h #o #g #G #L1 #L2 * -g -L1 -L2
[ #f #g #J #L1 #W #_ #H destruct
| #f #I #K1 #K2 #_ #g #J #L1 #W #H
  elim (discr_push_next … H)
| #f #I #K1 #K2 #_ #g #J #L1 #W #_ #H destruct
| #f #I #K1 #K2 #V #HV #HK12 #g #J #L1 #W #H1 #H2 destruct
  <(injective_next … H1) -g /2 width=4 by ex3_intro/
]
qed-.

(* Basic_2A1: uses: lcosx_inv_pair *)
lemma lsubsx_inv_pair_sn: ∀h,o,f,I,G,K1,L2,V. G ⊢ K1.ⓑ{I}V ⊆ⓧ[h, o, ↑f] L2 →
                          ∃∃K2. G ⊢ ⬈*[h, o, V] 𝐒⦃K2⦄ &
                                G ⊢ K1 ⊆ⓧ[h, o, f] K2 & L2 = K2.ⓧ.
/2 width=6 by lsubsx_inv_pair_sn_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsubsx_inv_pair_sn_gen: ∀h,o,g,I,G,K1,L2,V. G ⊢ K1.ⓑ{I}V ⊆ⓧ[h, o, g] L2 →
                              ∨∨ ∃∃f,K2. G ⊢ K1 ⊆ⓧ[h, o, f] K2 & g = ⫯f & L2 = K2.ⓑ{I}V
                               | ∃∃f,K2. G ⊢ ⬈*[h, o, V] 𝐒⦃K2⦄ &
                                         G ⊢ K1 ⊆ⓧ[h, o, f] K2 & g = ↑f & L2 = K2.ⓧ.
#h #o #g #I #G #K1 #L2 #V #H
elim (pn_split g) * #f #Hf destruct
[ elim (lsubsx_inv_push_sn … H) -H /3 width=5 by ex3_2_intro, or_introl/
| elim (lsubsx_inv_pair_sn … H) -H /3 width=6 by ex4_2_intro, or_intror/
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma lsubsx_fwd_bind_sn: ∀h,o,g,I1,G,K1,L2. G ⊢ K1.ⓘ{I1} ⊆ⓧ[h, o, g] L2 →
                          ∃∃I2,K2. G ⊢ K1 ⊆ⓧ[h, o, ⫱g] K2 & L2 = K2.ⓘ{I2}.
#h #o #g #I1 #G #K1 #L2
elim (pn_split g) * #f #Hf destruct
[ #H elim (lsubsx_inv_push_sn … H) -H
| cases I1 -I1 #I1
  [ #H elim (lsubsx_inv_unit_sn … H) -H
  | #V #H elim (lsubsx_inv_pair_sn … H) -H
  ]
]
/2 width=4 by ex2_2_intro/
qed-.

(* Basic properties *********************************************************)

lemma lsubsx_eq_repl_back: ∀h,o,G,L1,L2. eq_repl_back … (λf. G ⊢ L1 ⊆ⓧ[h, o, f] L2).
#h #o #G #L1 #L2 #f1 #H elim H -L1 -L2 -f1 //
[ #f #I #L1 #L2 #_ #IH #x #H
  elim (eq_inv_px … H) -H /3 width=3 by lsubsx_push/
| #f #I #L1 #L2 #_ #IH #x #H
  elim (eq_inv_nx … H) -H /3 width=3 by lsubsx_unit/
| #f #I #L1 #L2 #V #HV #_ #IH #x #H
  elim (eq_inv_nx … H) -H /3 width=3 by lsubsx_pair/
]
qed-.

lemma lsubsx_eq_repl_fwd: ∀h,o,G,L1,L2. eq_repl_fwd … (λf. G ⊢ L1 ⊆ⓧ[h, o, f] L2).
#h #o #G #L1 #L2 @eq_repl_sym /2 width=3 by lsubsx_eq_repl_back/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lcosx_O *)
lemma lsubsx_refl: ∀h,o,f,G. 𝐈⦃f⦄ → reflexive … (lsubsx h o G f).
#h #o #f #G #Hf #L elim L -L
/3 width=3 by lsubsx_eq_repl_back, lsubsx_push, eq_push_inv_isid/
qed.

(* Basic_2A1: removed theorems 2:
              lcosx_drop_trans_lt lcosx_inv_succ
*)
