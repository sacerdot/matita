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

include "basic_2/substitution/lleq_leq.ma".
include "basic_2/reduction/llpx_lleq.ma".
include "basic_2/computation/cpxs_lleq.ma".
include "basic_2/computation/llpxs_cpxs.ma".

(* LAZY SN EXTENDED PARALLEL COMPUTATION FOR LOCAL ENVIRONMENTS *************)

(* Properties on lazy equivalence for local environments ********************)

lemma llpxs_lrefl: ∀h,g,G,L1,L2,T,d. L1 ⋕[T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
/3 width=1 by llpx_lrefl, llpx_llpxs/ qed-.

lemma lleq_llpxs_trans: ∀h,g,G,L2,L,T,d. ⦃G, L2⦄ ⊢ ➡*[h, g, T, d] L →
                        ∀L1. L1 ⋕[T, d] L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L.
#h #g #G #L2 #L #T #d #H @(llpxs_ind … H) -L
/3 width=3 by llpxs_strap1, llpxs_lrefl/
qed-.

lemma lleq_llpxs_conf: ∀h,g,G,L1,L,T,d. ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L →
                       ∀L2. L1 ⋕[T, d] L2 → ⦃G, L2⦄ ⊢ ➡*[h, g, T, d] L.
/3 width=3 by lleq_llpxs_trans, lleq_sym/ qed-.
(*
foct leq_lpxs_trans_lleq_aux: ∀h,g,G,L1,L0,d,e. L1 ≃[d, e] L0 → e = ∞ →
                              ∀L2. ⦃G, L0⦄ ⊢ ➡*[h, g] L2 →
                              ∃∃L. L ≃[d, e] L2 & ⦃G, L1⦄ ⊢ ➡*[h, g] L &
                                   (∀T. L0 ⋕[T, d] L2 ↔ L1 ⋕[T, d] L).
#h #g #G #L1 #L0 #d #e #H elim H -L1 -L0 -d -e
[ #d #e #_ #L2 #H >(lpxs_inv_atom1 … H) -H
  /3 width=5 by ex3_intro, conj/
| #I1 #I0 #L1 #L0 #V1 #V0 #_ #_ #He destruct
| #I #L1 #L0 #V1 #e #HL10 #IHL10 #He #Y #H
  elim (lpxs_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  lapply (ysucc_inv_Y_dx … He) -He #He
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I}V2)) /3 width=3 by lpxs_pair, leq_cpxs_trans, leq_pair/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_leq_repl … H) -H /3 width=1 by leq_sym, leq_pair_O_Y/
| #I1 #I0 #L1 #L0 #V1 #V0 #d #e #HL10 #IHL10 #He #Y #H
  elim (lpxs_inv_pair1 … H) -H #L2 #V2 #HL02 #HV02 #H destruct
  elim (IHL10 … HL02) // -IHL10 -HL02 #L #HL2 #HL1 #IH
  @(ex3_intro … (L.ⓑ{I1}V1)) /3 width=1 by lpxs_pair, leq_succ/
  #T elim (IH T) #HL0dx #HL0sn
  @conj #H @(lleq_leq_repl … H) -H /3 width=1 by leq_sym, leq_succ/
]
qed-.

lamma leq_lpxs_trans_lleq: ∀h,g,G,L1,L0,d. L1 ≃[d, ∞] L0 →
                           ∀L2. ⦃G, L0⦄ ⊢ ➡*[h, g] L2 →
                           ∃∃L. L ≃[d, ∞] L2 & ⦃G, L1⦄ ⊢ ➡*[h, g] L &
                                (∀T. L0 ⋕[T, d] L2 ↔ L1 ⋕[T, d] L).
/2 width=1 by leq_lpxs_trans_lleq_aux/ qed-.
*)
