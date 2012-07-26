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

lemma append_length: ∀L1,L2. |L1 @@ L2| = |L1| + |L2|.
#L1 #L2 elim L2 -L2 normalize //
qed.

(* Basic inversion lemmas ***************************************************)

axiom discr_lpair_append_xy_x: ∀I,L,K,V. (L @@ K).ⓑ{I}V = L → ⊥.
(*
#I #L #K #V #H
lapply (refl … (|L|)) <H in ⊢ (? ? % ? → ?); -H
normalize >append_length -I -V #H
*)
lemma append_inv_sn: ∀L1,L2,L. L1 @@ L = L2 @@ L → L1 = L2.
#L1 #L2 #L elim L -L normalize //
#L #I #V #IHL #HL12 destruct /2 width=1/ (**) (* destruct does not simplify well *)
qed.

(* Note: lemma 750 *)
lemma append_inv_dx: ∀L1,L2,L. L @@ L1 = L @@ L2 → L1 = L2.
#L1 elim L1 -L1
[ * normalize //
  #L2 #I2 #V2 #L #H
  elim (discr_lpair_append_xy_x I2 L L2 V2 ?) //
| #L1 #I1 #V1 #IHL1 * normalize
  [ #L #H -IHL1 elim (discr_lpair_append_xy_x … H)
  | #L2 #I2 #V2 #L normalize #H destruct (**) (* destruct does not simplify well *)
    -H >e0 /3 width=2/
  ]
]
qed.
