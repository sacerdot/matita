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

(* THE FORMAL SYSTEM λδ - MATITA SOURCE FILES
 * Support for abstract candidates of reducibility closed: 2012 January 27
 * Confluence of context-sensitive parallel reduction closed: 2011 September 21
 * Confluence of context-free parallel reduction closed: 2011 September 6
 * Specification started: 2011 April 17
 * - Patience on me to gain peace and perfection! -
 * [ suggested invocation to start formal specifications with ]
 *)

include "Ground_2/star.ma".
include "Basic_2/notation.ma".

(* ATOMIC ARITY *************************************************************)

inductive aarity: Type[0] ≝
  | AAtom: aarity                   (* atomic aarity construction *)
  | APair: aarity → aarity → aarity (* binary aarity construction *)
.

interpretation "aarity construction (atomic)"
   'Item0 = AAtom.

interpretation "aarity construction (binary)"
   'SnItem2 A1 A2 = (APair A1 A2).

(* Basic inversion lemmas ***************************************************)

lemma discr_apair_xy_x: ∀A,B. ②B. A = B → False.
#A #B elim B -B
[ #H destruct
| #Y #X #IHY #_ #H destruct
  -H >e0 in e1; normalize (**) (* destruct: one quality is not simplified, the destucted equality is not erased *)
  /2 width=1/
]
qed-.

lemma discr_tpair_xy_y: ∀B,A. ②B. A = A → False.
#B #A elim A -A
[ #H destruct
| #Y #X #_ #IHX #H destruct
  -H (**) (* destruct: the destucted equality is not erased *)
  /2 width=1/
]
qed-.

(* Basic properties *********************************************************)

lemma aarity_eq_dec: ∀A1,A2:aarity. Decidable (A1 = A2).
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
