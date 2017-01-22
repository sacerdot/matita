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

include "basic_2/substitution/lleq_alt.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Advanced inversion lemmas ************************************************)

fact lleq_inv_S_aux: ∀L1,L2,T,d0. L1 ⋕[T, d0] L2 → ∀d. d0 = d + 1 →
                     ∀K1,K2,I,V. ⇩[d] L1 ≡ K1.ⓑ{I}V → ⇩[d] L2 ≡ K2.ⓑ{I}V →
                     K1 ⋕[V, 0] K2 → L1 ⋕[T, d] L2.
#L1 #L2 #T #d0 #H @(lleq_ind_alt … H) -L1 -L2 -T -d0
/2 width=1 by lleq_gref, lleq_free, lleq_sort/
[ #L1 #L2 #d0 #i #HL12 #Hid #d #H #K1 #K2 #I #V #HLK1 #HLK2 #HV destruct
  elim (yle_split_eq i d) /2 width=1 by lleq_skip, ylt_fwd_succ2/ -HL12 -Hid
  #H destruct /2 width=8 by lleq_lref/
| #I1 #I2 #L1 #L2 #K11 #K22 #V #d0 #i #Hd0i #HLK11 #HLK22 #HV #_ #d #H #K1 #K2 #J #W #_ #_ #_ destruct
  /3 width=8 by lleq_lref, yle_pred_sn/
| #a #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /4 width=7 by lleq_bind, ldrop_drop/
| #I #L1 #L2 #V #T #d0 #_ #_ #IHV #IHT #d #H #K1 #K2 #J #W #HLK1 #HLK2 destruct
  /3 width=7 by lleq_flat/
]
qed-.

lemma lleq_inv_S: ∀T,L1,L2,d. L1 ⋕[T, d+1] L2 →
                  ∀K1,K2,I,V. ⇩[d] L1 ≡ K1.ⓑ{I}V → ⇩[d] L2 ≡ K2.ⓑ{I}V →
                  K1 ⋕[V, 0] K2 → L1 ⋕[T, d] L2.
/2 width=7 by lleq_inv_S_aux/ qed-.

lemma lleq_inv_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[ⓑ{a,I}V.T, 0] L2 →
                       L1 ⋕[V, 0] L2 ∧ L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V.
#a #I #L1 #L2 #V #T #H elim (lleq_inv_bind … H) -H
/3 width=7 by ldrop_pair, conj, lleq_inv_S/
qed-.

(* Advanced forward lemmas **************************************************)

lemma lleq_fwd_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[ⓑ{a,I}V.T, 0] L2 →
                       L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V.
#a #I #L1 #L2 #V #T #H elim (lleq_inv_bind_O … H) -H //
qed-.

(* Advanced properties ******************************************************)

lemma lleq_ge: ∀L1,L2,T,d1. L1 ⋕[T, d1] L2 → ∀d2. d1 ≤ d2 → L1 ⋕[T, d2] L2.
#L1 #L2 #T #d1 #H @(lleq_ind_alt … H) -L1 -L2 -T -d1
/4 width=1 by lleq_sort, lleq_free, lleq_gref, lleq_bind, lleq_flat, yle_succ/
[ /3 width=3 by lleq_skip, ylt_yle_trans/
| #I1 #I2 #L1 #L2 #K1 #K2 #V #d1 #i #Hi #HLK1 #HLK2 #HV #IHV #d2 #Hd12 elim (ylt_split i d2)
  [ lapply (lleq_fwd_length … HV) #HK12 #Hid2
    lapply (ldrop_fwd_length … HLK1) lapply (ldrop_fwd_length … HLK2)
    normalize in ⊢ (%→%→?); -I1 -I2 -V -d1 /2 width=1 by lleq_skip/ 
  | /3 width=8 by lleq_lref, yle_trans/
  ]
]
qed-.

lemma lleq_bind_O: ∀a,I,L1,L2,V,T. L1 ⋕[V, 0] L2 → L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V →
                   L1 ⋕[ⓑ{a,I}V.T, 0] L2.
/3 width=3 by lleq_ge, lleq_bind/ qed.

lemma lleq_bind_repl_SO: ∀I1,I2,L1,L2,V1,V2,T. L1.ⓑ{I1}V1 ⋕[T, 0] L2.ⓑ{I2}V2 →
                         ∀J1,J2,W1,W2. L1.ⓑ{J1}W1 ⋕[T, 1] L2.ⓑ{J2}W2.
#I1 #I2 #L1 #L2 #V1 #V2 #T #HT #J1 #J2 #W1 #W2 lapply (lleq_ge … HT 1 ?) // -HT
#HT @(lleq_lsuby_repl … HT) /2 width=1 by lsuby_succ/ (**) (* full auto fails *)
qed-.

lemma lleq_bind_repl_O: ∀I,L1,L2,V,T. L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V →
                        ∀J,W. L1 ⋕[W, 0] L2 → L1.ⓑ{J}W ⋕[T, 0] L2.ⓑ{J}W.
/3 width=7 by lleq_bind_repl_SO, lleq_inv_S/ qed-.

(* Inversion lemmas on negated lazy quivalence for local environments *******)

lemma nlleq_inv_bind_O: ∀a,I,L1,L2,V,T. (L1 ⋕[ⓑ{a,I}V.T, 0] L2 → ⊥) →
                        (L1 ⋕[V, 0] L2 → ⊥) ∨ (L1.ⓑ{I}V ⋕[T, 0] L2.ⓑ{I}V → ⊥).
#a #I #L1 #L2 #V #T #H elim (lleq_dec V L1 L2 0)
/4 width=1 by lleq_bind_O, or_intror, or_introl/
qed-.
