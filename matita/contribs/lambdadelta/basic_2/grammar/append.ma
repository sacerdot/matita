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

include "ground_2/notation/functions/append_2.ma".
include "basic_2/notation/functions/snbind2_3.ma".
include "basic_2/notation/functions/snabbr_2.ma".
include "basic_2/notation/functions/snabst_2.ma".
include "basic_2/grammar/lenv.ma".

(* APPEND FOR LOCAL ENVIRONMENTS ********************************************)

rec definition append L K on K ≝ match K with
[ LAtom       ⇒ L
| LPair K I V ⇒ (append L K).ⓑ{I}V
].

interpretation "append (local environment)" 'Append L1 L2 = (append L1 L2).

interpretation "local environment tail binding construction (binary)"
   'SnBind2 I T L = (append (LPair LAtom I T) L).

interpretation "tail abbreviation (local environment)"
   'SnAbbr T L = (append (LPair LAtom Abbr T) L).

interpretation "tail abstraction (local environment)"
   'SnAbst L T = (append (LPair LAtom Abst T) L).

definition d_appendable_sn: predicate (lenv→relation term) ≝ λR.
                            ∀K,T1,T2. R K T1 T2 → ∀L. R (L@@K) T1 T2.

(* Basic properties *********************************************************)

lemma append_atom: ∀L. L @@ ⋆ = L.
// qed.

lemma append_pair: ∀I,L,K,V. L@@(K.ⓑ{I}V) = (L@@K).ⓑ{I}V.
// qed.

lemma append_atom_sn: ∀L. ⋆@@L = L.
#L elim L -L //
#L #I #V >append_pair //
qed.

lemma append_assoc: associative … append.
#L1 #L2 #L3 elim L3 -L3 //
qed.

lemma append_shift: ∀L,K,I,V. L@@(ⓑ{I}V.K) = (L.ⓑ{I}V)@@K.
#L #K #I #V <append_assoc //
qed.

(* Basic inversion lemmas ***************************************************)

lemma append_inj_sn: ∀K,L1,L2. L1@@K = L2@@K → L1 = L2.
#K elim K -K //
#K #I #V #IH #L1 #L2 >append_pair #H
elim (destruct_lpair_lpair_aux … H) -H /2 width=1 by/ (**) (* destruct lemma needed *)
qed-.
