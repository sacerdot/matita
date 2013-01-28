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

(* LOCAL ENVIRONMENTS *******************************************************)

let rec append L K on K ≝ match K with
[ LAtom       ⇒ L
| LPair K I V ⇒ (append L K). ⓑ{I} V
].

interpretation "append (local environment)" 'Append L1 L2 = (append L1 L2).

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

(* Basic inversion lemmas ***************************************************)

lemma append_inj_sn: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |K1| = |K2| →
                     L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * normalize /2 width=1/
  #K2 #I2 #V2 #L1 #L2 #_ <plus_n_Sm #H destruct
| #K1 #I1 #V1 #IH * normalize
  [ #L1 #L2 #_ <plus_n_Sm #H destruct
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1 ?) -IH -H1 // -H2 /2 width=1/
  ]
]
qed-.

(* Note: lemma 750 *)
lemma append_inj_dx: ∀K1,K2,L1,L2. L1 @@ K1 = L2 @@ K2 → |L1| = |L2| →
                     L1 = L2 ∧ K1 = K2.
#K1 elim K1 -K1
[ * normalize /2 width=1/
  #K2 #I2 #V2 #L1 #L2 #H1 #H2 destruct
  normalize in H2; >append_length in H2; #H
  elim (plus_xySz_x_false … H)
| #K1 #I1 #V1 #IH * normalize
  [ #L1 #L2 #H1 #H2 destruct
    normalize in H2; >append_length in H2; #H
    elim (plus_xySz_x_false … (sym_eq … H))
  | #K2 #I2 #V2 #L1 #L2 #H1 #H2
    elim (destruct_lpair_lpair … H1) -H1 #H1 #H3 #H4 destruct (**) (* destruct lemma needed *)
    elim (IH … H1 ?) -IH -H1 // -H2 /2 width=1/
  ]
]
qed-.

lemma append_inv_refl_dx: ∀L,K. L @@ K = L → K = ⋆.
#L #K #H
elim (append_inj_dx … (⋆) … H ?) //
qed-.

lemma append_inv_pair_dx: ∀I,L,K,V. L @@ K = L.ⓑ{I}V → K = ⋆.ⓑ{I}V.
#I #L #K #V #H
elim (append_inj_dx … (⋆.ⓑ{I}V) … H ?) //
qed-.

lemma length_inv_pos_dx_append: ∀d,L. |L| = d + 1 →
                                ∃∃I,K,V. |K| = d & L = ⋆.ⓑ{I}V @@ K.
#d @(nat_ind_plus … d) -d
[ #L #H 
  elim (length_inv_pos_dx … H) -H #I #K #V #H
  >(length_inv_zero_dx … H) -H #H destruct
  @ex2_3_intro [4: /2 width=2/ |5: // |1,2,3: skip ] (**) (* /3/ does not work *)
| #d #IHd #L #H
  elim (length_inv_pos_dx … H) -H #I #K #V #H
  elim (IHd … H) -IHd -H #I0 #K0 #V0 #H1 #H2 #H3 destruct
  @(ex2_3_intro … (K0.ⓑ{I}V)) //
]
qed-.

(* Basic_eliminators ********************************************************)

fact lenv_ind_dx_aux: ∀R:predicate lenv. R (⋆) →
                      (∀I,L,V. R L → R (⋆.ⓑ{I}V @@ L)) →
                      ∀d,L. |L| = d → R L.
#R #Hatom #Hpair #d @(nat_ind_plus … d) -d
[ #L #H >(length_inv_zero_dx … H) -H //
| #d #IH #L #H
  elim (length_inv_pos_dx_append … H) -H #I #K #V #H1 #H2 destruct /3 width=1/
]
qed-.

lemma lenv_ind_dx: ∀R:predicate lenv. R (⋆) →
                   (∀I,L,V. R L → R (⋆.ⓑ{I}V @@ L)) →
                   ∀L. R L.
/3 width=2 by lenv_ind_dx_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma length_inv_pos_sn_append: ∀d,L. 1 + d = |L| →
                                ∃∃I,K,V. d = |K| & L = ⋆. ⓑ{I}V @@ K.
#d >commutative_plus @(nat_ind_plus … d) -d
[ #L #H elim (length_inv_pos_sn … H) -H #I #K #V #H1 #H2 destruct
  >(length_inv_zero_sn … H1) -K
  @(ex2_3_intro … (⋆)) // (**) (* explicit constructor *)
| #d #IHd #L #H elim (length_inv_pos_sn … H) -H #I #K #V #H1 #H2 destruct
  >H1 in IHd; -H1 #IHd
  elim (IHd K ?) -IHd // #J #L #W #H1 #H2 destruct
  @(ex2_3_intro … (L.ⓑ{I}V)) // (**) (* explicit constructor *)
  >append_length /2 width=1/
]
qed-.
