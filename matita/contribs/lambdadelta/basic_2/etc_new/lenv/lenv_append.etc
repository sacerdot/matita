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
include "ground_2/ynat/ynat_plus.ma".
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

definition d_appendable_sn: predicate (lenv→relation term) ≝ λR.
                            ∀K,T1,T2. R K T1 T2 → ∀L. R (L @@ K) T1 T2.

(* Basic properties *********************************************************)

lemma append_atom: ∀L. L @@ ⋆ = L.
// qed.

lemma append_pair: ∀I,L,K,V. L @@ (K.ⓑ{I}V) = (L @@ K).ⓑ{I}V.
// qed.

lemma append_atom_sn: ∀L. ⋆ @@ L = L.
#L elim L -L //
#L #I #V >append_pair //
qed.

lemma append_assoc: associative … append.
#L1 #L2 #L3 elim L3 -L3 //
qed.

lemma append_length: ∀L1,L2. |L1 @@ L2| = |L1| + |L2|.
#L1 #L2 elim L2 -L2 //
#L2 #I #V2 >append_pair >length_pair >length_pair //
qed.

lemma ltail_length: ∀I,L,V. |ⓑ{I}V.L| = ⫯|L|.
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
[ * /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 #_ >length_atom >length_pair
  #H elim (ysucc_inv_O_sn … H)
| #K1 #I1 #V1 #IH *
  [ #L1 #L2 #_ >length_atom >length_pair
    #H elim (ysucc_inv_O_dx … H)
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair_aux … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /3 width=1 by ysucc_inv_inj, conj/
  ]
]
qed-.

(* Note: lemma 750 *)
lemma append_inj_dx: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |L1| = |L2| →
                     L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 >append_atom >append_pair #H destruct
  >length_pair >append_length <yplus_succ2 #H
  elim (discr_yplus_xy_x … H) -H #H
  [ elim (ylt_yle_false (|L2|) (∞)) // | elim (ysucc_inv_O_dx … H) ]
| #K1 #I1 #V1 #IH *
  [ #L1 #L2 >append_pair >append_atom #H destruct
    >length_pair >append_length <yplus_succ2 #H
    elim (discr_yplus_x_xy … H) -H #H
    [ elim (ylt_yle_false (|L1|) (∞)) // | elim (ysucc_inv_O_dx … H) ]
  | #K2 #I2 #V2 #L1 #L2 >append_pair >append_pair #H1 #H2
    elim (destruct_lpair_lpair_aux … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
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

lemma length_inv_pos_dx_ltail: ∀L,l. |L| = ⫯l →
                               ∃∃I,K,V. |K| = l & L = ⓑ{I}V.K.
#Y #l #H elim (length_inv_pos_dx … H) -H #I #L #V #Hl #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

lemma length_inv_pos_sn_ltail: ∀L,l. ⫯l = |L| →
                               ∃∃I,K,V. l = |K| & L = ⓑ{I}V.K.
#Y #l #H elim (length_inv_pos_sn … H) -H #I #L #V #Hl #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

(* Basic eliminators ********************************************************)

(* Basic_1: was: c_tail_ind *)
lemma lenv_ind_alt: ∀R:predicate lenv.
                    R (⋆) → (∀I,L,T. R L → R (ⓑ{I}T.L)) →
                    ∀L. R L.
#R #IH1 #IH2 #L @(ynat_f_ind … length … L) -L #x #IHx * // -IH1
#L #I #V #H destruct elim (lpair_ltail L I V)
/4 width=1 by monotonic_ylt_plus_sn/
qed-.
