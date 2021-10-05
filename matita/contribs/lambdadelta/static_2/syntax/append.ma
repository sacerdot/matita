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

include "ground/xoa/ex_1_2.ma".
include "static_2/notation/functions/snitem_2.ma".
include "static_2/notation/functions/snbind1_2.ma".
include "static_2/notation/functions/snbind2_3.ma".
include "static_2/notation/functions/snvoid_1.ma".
include "static_2/notation/functions/snabbr_2.ma".
include "static_2/notation/functions/snabst_2.ma".
include "static_2/syntax/lenv.ma".

(* APPEND FOR LOCAL ENVIRONMENTS ********************************************)

rec definition append L K on K ≝ match K with
[ LAtom     ⇒ L
| LBind K I ⇒ (append L K).ⓘ[I]
].

interpretation "append (local environment)" 'nplus L1 L2 = (append L1 L2).

interpretation "local environment tail binding construction (generic)"
   'SnItem I L = (append (LBind LAtom I) L).

interpretation "local environment tail binding construction (unary)"
   'SnBind1 I L = (append (LBind LAtom (BUnit I)) L).

interpretation "local environment tail binding construction (binary)"
   'SnBind2 I T L = (append (LBind LAtom (BPair I T)) L).

interpretation "tail exclusion (local environment)"
   'SnVoid L = (append (LBind LAtom (BUnit Void)) L).

interpretation "tail abbreviation (local environment)"
   'SnAbbr T L = (append (LBind LAtom (BPair Abbr T)) L).

interpretation "tail abstraction (local environment)"
   'SnAbst L T = (append (LBind LAtom (BPair Abst T)) L).

definition d_appendable_sn: predicate (lenv→relation term) ≝ λR.
                            ∀K,T1,T2. R K T1 T2 → ∀L. R (L+K) T1 T2.

(* Basic properties *********************************************************)

lemma append_atom: ∀L. (L + ⋆) = L. (**) (* () should be redundant *)
// qed.

(* Basic_2A1: uses: append_pair *)
lemma append_bind: ∀I,L,K. L+(K.ⓘ[I]) = (L+K).ⓘ[I].
// qed.

lemma append_atom_sn: ∀L. ⋆ + L = L.
#L elim L -L //
#L #I >append_bind //
qed.

lemma append_assoc: associative … append.
#L1 #L2 #L3 elim L3 -L3 //
qed.

lemma append_shift: ∀L,K,I. L+(ⓘ[I].K) = (L.ⓘ[I])+K.
#L #K #I <append_assoc //
qed.

(* Basic inversion lemmas ***************************************************)

lemma append_inv_atom3_sn: ∀L,K. ⋆ = L + K → ∧∧ ⋆ = L & ⋆ = K.
#L * /2 width=1 by conj/
#K #I >append_bind #H destruct
qed-.

lemma append_inv_bind3_sn: ∀I0,L,L0,K. L0.ⓘ[I0] = L + K →
                           ∨∨ ∧∧ L0.ⓘ[I0] = L & ⋆ = K
                            | ∃∃K0. K = K0.ⓘ[I0] & L0 = L + K0.
#I0 #L #L0 * /3 width=1 by or_introl, conj/
#K #I >append_bind #H destruct /3 width=3 by ex2_intro, or_intror/
qed-.

lemma append_inj_sn: ∀K,L1,L2. L1+K = L2+K → L1 = L2.
#K elim K -K //
#K #I #IH #L1 #L2 >append_bind #H
elim (destruct_lbind_lbind_aux … H) -H /2 width=1 by/ (**) (* destruct lemma needed *)
qed-.

(* Basic_1: uses: chead_ctail *)
(* Basic_2A1: uses: lpair_ltail *)
lemma lenv_case_tail: ∀L. L = ⋆ ∨ ∃∃K,I. L = ⓘ[I].K.
#L elim L -L /2 width=1 by or_introl/
#L #I * [2: * ] /3 width=3 by ex1_2_intro, or_intror/
qed-.
