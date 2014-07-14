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

(* THE FORMAL SYSTEM λδ: MATITA SOURCE FILES
 * Initial invocation: - Patience on me to gain peace and perfection! -
 *)

include "ground_2/lib/star.ma".
include "basic_2/notation/constructors/item0_0.ma".
include "basic_2/notation/constructors/snitem2_2.ma".

(* ATOMIC ARITY *************************************************************)

inductive aarity: Type[0] ≝
  | AAtom: aarity                   (* atomic aarity construction *)
  | APair: aarity → aarity → aarity (* binary aarity construction *)
.

interpretation "atomic arity construction (atomic)"
   'Item0 = AAtom.

interpretation "atomic arity construction (binary)"
   'SnItem2 A1 A2 = (APair A1 A2).

(* Basic inversion lemmas ***************************************************)

lemma discr_apair_xy_x: ∀A,B. ②B. A = B → ⊥.
#A #B elim B -B
[ #H destruct
| #Y #X #IHY #_ #H destruct
  -H >e0 in e1; normalize (**) (* destruct: one quality is not simplified, the destructed equality is not erased *)
  /2 width=1/
]
qed-.

lemma discr_tpair_xy_y: ∀B,A. ②B. A = A → ⊥.
#B #A elim A -A
[ #H destruct
| #Y #X #_ #IHX #H destruct
  -H (**) (* destruct: the destructed equality is not erased *)
  /2 width=1/
]
qed-.

(* Basic properties *********************************************************)

lemma eq_aarity_dec: ∀A1,A2:aarity. Decidable (A1 = A2).
#A1 elim A1 -A1
[ #A2 elim A2 -A2 /2 width=1/
  #B2 #A2 #_ #_ @or_intror #H destruct
| #B1 #A1 #IHB1 #IHA1 #A2 elim A2 -A2
  [ -IHB1 -IHA1 @or_intror #H destruct
  | #B2 #A2 #_ #_ elim (IHB1 B2) -IHB1
    [ #H destruct elim (IHA1 A2) -IHA1
      [ #H destruct /2 width=1/
      | #HA12 @or_intror #H destruct /2 width=1/
      ]
    | -IHA1 #HB12 @or_intror #H destruct /2 width=1/
    ]
  ]
]
qed-.
