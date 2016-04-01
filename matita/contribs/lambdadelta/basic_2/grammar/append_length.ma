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

include "basic_2/grammar/lenv_length.ma".
include "basic_2/grammar/append.ma".

(* APPEND FOR LOCAL ENVIRONMENTS ********************************************)

(* Properties with length for local environments ****************************)

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
@(ex2_3_intro … J (K.ⓑ{I}V) W) /2 width=1 by length_pair/
qed-.

(* Advanced inversion lemmas on length for local environments ***************)

(* Basic_2A1: was: length_inv_pos_dx_ltail *)
lemma length_inv_succ_dx_ltail: ∀L,l. |L| = ⫯l →
                               ∃∃I,K,V. |K| = l & L = ⓑ{I}V.K.
#Y #l #H elim (length_inv_succ_dx … H) -H #I #L #V #Hl #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

(* Basic_2A1: was: length_inv_pos_sn_ltail *)
lemma length_inv_succ_sn_ltail: ∀L,l. ⫯l = |L| →
                               ∃∃I,K,V. l = |K| & L = ⓑ{I}V.K.
#Y #l #H elim (length_inv_succ_sn … H) -H #I #L #V #Hl #HLK destruct
elim (lpair_ltail L I V) /2 width=5 by ex2_3_intro/
qed-.

(* Inversion lemmas with length for local environments **********************)

(* Basic_2A1: was: append_inj_sn *)
lemma append_inj_length_sn: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |K1| = |K2| →
                            L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 #_ >length_atom >length_pair
  #H destruct
| #K1 #I1 #V1 #IH *
  [ #L1 #L2 #_ >length_atom >length_pair
    #H destruct
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair_aux … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /2 width=1 by conj/
  ]
]
qed-.

(* Note: lemma 750 *)
(* Basic_2A1: was: append_inj_dx *)
lemma append_inj_length_dx: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |L1| = |L2| →
                            L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * /2 width=1 by conj/
  #K2 #I2 #V2 #L1 #L2 >append_atom >append_pair #H destruct
  >length_pair >append_length >plus_n_Sm
  #H elim (plus_xSy_x_false … H)
| #K1 #I1 #V1 #IH *
  [ #L1 #L2 >append_pair >append_atom #H destruct
    >length_pair >append_length >plus_n_Sm #H
    lapply (discr_plus_x_xy … H) -H #H destruct
  | #K2 #I2 #V2 #L1 #L2 >append_pair >append_pair #H1 #H2
    elim (destruct_lpair_lpair_aux … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /2 width=1 by conj/
  ]
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma append_inj_dx: ∀L,K1,K2. L@@K1 = L@@K2 → K1 = K2.
#L #K1 #K2 #H elim (append_inj_length_dx … H) -H //
qed-.

lemma append_inv_refl_dx: ∀L,K. L@@K = L → K = ⋆.
#L #K #H elim (append_inj_dx … (⋆) … H) //
qed-.

lemma append_inv_pair_dx: ∀I,L,K,V. L@@K = L.ⓑ{I}V → K = ⋆.ⓑ{I}V.
#I #L #K #V #H elim (append_inj_dx … (⋆.ⓑ{I}V) … H) //
qed-.

(* Basic eliminators ********************************************************)

(* Basic_1: was: c_tail_ind *)
lemma lenv_ind_alt: ∀R:predicate lenv.
                    R (⋆) → (∀I,L,T. R L → R (ⓑ{I}T.L)) →
                    ∀L. R L.
#R #IH1 #IH2 #L @(f_ind … length … L) -L #x #IHx * // -IH1
#L #I #V #H destruct elim (lpair_ltail L I V) /4 width=1 by/
qed-.
