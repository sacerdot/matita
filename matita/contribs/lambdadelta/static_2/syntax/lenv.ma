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

include "static_2/notation/functions/star_0.ma".
include "static_2/notation/functions/dxitem_2.ma".
include "static_2/notation/functions/dxbind1_2.ma".
include "static_2/notation/functions/dxbind2_3.ma".
include "static_2/notation/functions/dxvoid_1.ma".
include "static_2/notation/functions/dxabbr_2.ma".
include "static_2/notation/functions/dxabst_2.ma".
include "static_2/syntax/bind.ma".

(* LOCAL ENVIRONMENTS *******************************************************)

(* local environments *)
inductive lenv: Type[0] ≝
| LAtom: lenv               (* empty *)
| LBind: lenv → bind → lenv (* binding construction *)
.

interpretation "sort (local environment)"
   'Star = LAtom.

interpretation "local environment binding construction (generic)"
   'DxItem L I = (LBind L I).

interpretation "local environment binding construction (unary)"
   'DxBind1 L I = (LBind L (BUnit I)).

interpretation "local environment binding construction (binary)"
   'DxBind2 L I T = (LBind L (BPair I T)).

interpretation "void (local environment)"
   'DxVoid L = (LBind L (BUnit Void)).

interpretation "abbreviation (local environment)"
   'DxAbbr L T = (LBind L (BPair Abbr T)).

interpretation "abstraction (local environment)"
   'DxAbst L T = (LBind L (BPair Abst T)).

definition cfull: relation3 lenv bind bind ≝ λL,I1,I2. ⊤.

definition ceq: relation3 lenv term term ≝ λL. eq ….

(* Basic properties *********************************************************)

lemma eq_lenv_dec: ∀L1,L2:lenv. Decidable (L1 = L2).
#L1 elim L1 -L1 [| #L1 #I1 #IHL1 ] * [2,4: #L2 #I2 ]
[3: /2 width=1 by or_introl/
|2: elim (eq_bind_dec I1 I2) #HI
    [ elim (IHL1 L2) -IHL1 #HL /2 width=1 by or_introl/ ]
]
@or_intror #H destruct /2 width=1 by/
qed-.

lemma cfull_dec: ∀L,T1,T2. Decidable (cfull L T1 T2).
/2 width=1 by or_introl/ qed-.

(* Basic inversion lemmas ***************************************************)

fact destruct_lbind_lbind_aux: ∀I1,I2,L1,L2. L1.ⓘ{I1} = L2.ⓘ{I2} →
                               L1 = L2 ∧ I1 = I2.
#I1 #I2 #L1 #L2 #H destruct /2 width=1 by conj/
qed-.

(* Basic_2A1: uses: discr_lpair_x_xy *)
lemma discr_lbind_x_xy: ∀I,L. L = L.ⓘ{I} → ⊥.
#I #L elim L -L
[ #H destruct
| #L #J #IHL #H elim (destruct_lbind_lbind_aux … H) -H  (**) (* destruct lemma needed *)
  #H1 #H2 destruct /2 width=1 by/
]
qed-.

(* Basic_2A1: uses: discr_lpair_xy_x *)
lemma discr_lbind_xy_x: ∀I,L. L.ⓘ{I} = L → ⊥.
/2 width=4 by discr_lbind_x_xy/ qed-.
