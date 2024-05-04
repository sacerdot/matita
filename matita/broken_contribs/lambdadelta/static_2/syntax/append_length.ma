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

include "ground/arith/nat_plus.ma".
include "ground/arith/wf1_ind_nlt.ma".
include "static_2/syntax/lenv_length.ma".
include "static_2/syntax/append.ma".

(* APPEND FOR LOCAL ENVIRONMENTS ********************************************)

(* Properties with length for local environments ****************************)

lemma append_length: ∀L1,L2. |L1 + L2| = |L1| + |L2|.
#L1 #L2 elim L2 -L2 //
#L2 #I >append_bind >length_bind >length_bind //
qed.

lemma ltail_length: ∀I,L. |ⓘ[I].L| = ↑|L|.
#I #L >append_length //
qed.

(* Advanced inversion lemmas on length for local environments ***************)

(* Basic_2A1: was: length_inv_pos_dx_ltail *)
lemma length_inv_succ_dx_ltail: ∀L,n. |L| = ↑n →
                                ∃∃I,K. |K| = n & L = ⓘ[I].K.
#Y #n #H elim (length_inv_succ_dx … H) -H #I #L #Hn #HLK destruct
elim (lenv_case_tail … L) [| * #K #J ] #H destruct
/2 width=4 by ex2_2_intro/
@(ex2_2_intro … (J) (K.ⓘ[I])) // (**) (* auto fails *)
>ltail_length >length_bind //
qed-.

(* Basic_2A1: was: length_inv_pos_sn_ltail *)
lemma length_inv_succ_sn_ltail: ∀L,n. ↑n = |L| →
                                ∃∃I,K. n = |K| & L = ⓘ[I].K.
#Y #n #H elim (length_inv_succ_sn … H) -H #I #L #Hn #HLK destruct
elim (lenv_case_tail … L) [| * #K #J ] #H destruct
/2 width=4 by ex2_2_intro/
@(ex2_2_intro … (J) (K.ⓘ[I])) // (**) (* auto fails *)
>ltail_length >length_bind //
qed-.

(* Inversion lemmas with length for local environments **********************)

(* Basic_2A1: was: append_inj_sn *)
lemma append_inj_length_sn: ∀K1,K2,L1,L2. L1 + K1 = L2 + K2 → |K1| = |K2| →
                            ∧∧ L1 = L2 & K1 = K2.
#K1 elim K1 -K1
[ * /2 width=1 by conj/
  #K2 #I2 #L1 #L2 #_ >length_atom >length_bind
  #H elim (eq_inv_zero_nsucc … H)
| #K1 #I1 #IH *
  [ #L1 #L2 #_ >length_atom >length_bind
    #H elim (eq_inv_nsucc_zero … H)
  | #K2 #I2 #L1 #L2 #H1 >length_bind >length_bind #H2
    lapply (eq_inv_nsucc_bi … H2) -H2 #H2
    elim (destruct_lbind_lbind_aux … H1) -H1 #H1 #H3 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /3 width=4 by conj/
  ]
]
qed-.

(* Note: lemma 750 *)
(* Basic_2A1: was: append_inj_dx *)
lemma append_inj_length_dx: ∀K1,K2,L1,L2. L1 + K1 = L2 + K2 → |L1| = |L2| →
                            ∧∧ L1 = L2 & K1 = K2.
#K1 elim K1 -K1
[ * /2 width=1 by conj/
  #K2 #I2 #L1 #L2 >append_atom >append_bind #H destruct
  >length_bind >append_length #H
  elim (succ_nplus_refl_sn (|L2|) (|K2|) ?) //
| #K1 #I1 #IH *
  [ #L1 #L2 >append_bind >append_atom #H destruct
    >length_bind >append_length #H
    elim (succ_nplus_refl_sn … H)
  | #K2 #I2 #L1 #L2 >append_bind >append_bind #H1 #H2
    elim (destruct_lbind_lbind_aux … H1) -H1 #H1 #H3 destruct (**) (* destruct lemma needed *)
    elim (IH … H1) -IH -H1 /2 width=1 by conj/
  ]
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma append_inj_dx: ∀L,K1,K2. L+K1 = L+K2 → K1 = K2.
#L #K1 #K2 #H elim (append_inj_length_dx … H) -H //
qed-.

lemma append_inv_refl_dx: ∀L,K. L+K = L → K = ⋆.
#L #K #H elim (append_inj_dx … (⋆) … H) //
qed-.

lemma append_inv_pair_dx: ∀I,L,K,V. L+K = L.ⓑ[I]V → K = ⋆.ⓑ[I]V.
#I #L #K #V #H elim (append_inj_dx … (⋆.ⓑ[I]V) … H) //
qed-.

(* Basic eliminators ********************************************************)

(* Basic_1: was: c_tail_ind *)
(* Basic_2A1: was: lenv_ind_alt *)
lemma lenv_ind_tail: ∀Q:predicate lenv.
                     Q (⋆) → (∀I,L. Q L → Q (ⓘ[I].L)) → ∀L. Q L.
#Q #IH1 #IH2 #L @(wf1_ind_nlt … length … L) -L #x #IHx * //
#L #I -IH1 #H destruct
elim (lenv_case_tail … L) [| * #K #J ]
#H destruct /3 width=1 by/
qed-.
