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
include "basic_2/grammar/lenv_length.ma".

(* LOCAL ENVIRONMENTS *******************************************************)

let rec append L K on K ≝ match K with
[ LAtom       ⇒ L
| LPair K I V ⇒ (append L K). ⓑ{I} V
].

interpretation "append (local environment)" 'Append L1 L2 = (append L1 L2).

interpretation "local environment tail binding construction (binary)"
   'SnBind2 I T L = (append (LPair LAtom I T) L).

interpretation "tail abbreviation (local environment)"
   'SnAbbr T L = (append (LPair LAtom Abbr T) L).

interpretation "tail abstraction (local environment)"
   'SnAbst L T = (append (LPair LAtom Abst T) L).

definition l_appendable_sn: predicate (lenv→relation term) ≝ λR.
                            ∀K,T1,T2. R K T1 T2 → ∀L. R (L @@ K) T1 T2.

(* Basic properties *********************************************************)

lemma append_atom_sn: ∀L. ⋆ @@ L = L.
#L elim L -L normalize //
qed.

lemma append_assoc: associative … append.
#L1 #L2 #L3 elim L3 -L3 normalize //
qed.

lemma append_length: ∀L1,L2. |L1 @@ L2| = |L1| + |L2|.
#L1 #L2 elim L2 -L2 normalize //
qed.

lemma ltail_length: ∀I,L,V. |ⓑ{I}V.L| = |L| + 1.
#I #L #V >append_length //
qed.

(* Basic_1: was just: chead_ctail *)
lemma lpair_ltail: ∀L,I,V. ∃∃J,K,W. L.ⓑ{I}V = ⓑ{J}W.K & |L| = |K|.
#L elim L -L /2 width=5 by ex2_3_intro/
#L #Z #X #IHL #I #V elim (IHL Z X) -IHL
#J #K #W #H #_ >H -H >ltail_length
@(ex2_3_intro … J (K.ⓑ{I}V) W) //
qed-.

(* Basic inversion lemmas ***************************************************)

lemma append_inj_sn: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |K1| = |K2| →
                     L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * normalize /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 #_ <plus_n_Sm #H destruct
| #K1 #I1 #V1 #IH * normalize
  [ #L1 #L2 #_ <plus_n_Sm #H destruct
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /2 width=1 by conj/
  ]
]
qed-.

(* Note: lemma 750 *)
lemma append_inj_dx: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |L1| = |L2| →
                     L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * normalize /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 #H1 #H2 destruct
  normalize in H2; >append_length in H2; #H
  elim (plus_xySz_x_false … H)
| #K1 #I1 #V1 #IH * normalize
  [ #L1 #L2 #H1 #H2 destruct
    normalize in H2; >append_length in H2; #H
    elim (plus_xySz_x_false … (sym_eq … H))
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /2 width=1 by conj/
  ]
]
qed-.

lemma append_inv_refl_dx: ∀L,K. L @@ K = L → K = ⋆.
#L #K #H elim (append_inj_dx … (⋆) … H) //
qed-.

lemma append_inv_pair_dx: ∀I,L,K,V. L @@ K = L.ⓑ{I}V → K = ⋆.ⓑ{I}V.
#I #L #K #V #H elim (append_inj_dx … (⋆.ⓑ{I}V) … H) //
qed-.

lemma length_inv_pos_dx_ltail: ∀L,d. |L| = d + 1 →
                               ∃∃I,K,V. |K| = d & L = ⓑ{I}V.K.
#Y #d #H elim (length_inv_pos_dx … H) -H #I #L #V #Hd #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

lemma length_inv_pos_sn_ltail: ∀L,d. d + 1 = |L| →
                               ∃∃I,K,V. d = |K| & L = ⓑ{I}V.K.
#Y #d #H elim (length_inv_pos_sn … H) -H #I #L #V #Hd #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

(* Basic eliminators ********************************************************)

(* Basic_1: was: c_tail_ind *)
lemma lenv_ind_alt: ∀R:predicate lenv.
                    R (⋆) → (∀I,L,T. R L → R (ⓑ{I}T.L)) →
                    ∀L. R L.
#R #IH1 #IH2 #L @(f_ind … length … L) -L #n #IHn * // -IH1
#L #I #V normalize #H destruct elim (lpair_ltail L I V) /3 width=1 by/
qed-.
