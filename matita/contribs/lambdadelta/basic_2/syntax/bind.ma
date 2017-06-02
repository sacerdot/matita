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

include "basic_2/syntax/term.ma".

(* BINDERS FOR LOCAL ENVIRONMENTS ******************************************)

inductive bind: Type[0] ≝
| BUnit: bind1 → bind
| BPair: bind2 → term → bind
.

(* Basic properties ********************************************************)

lemma eq_bind_dec: ∀I1,I2:bind. Decidable (I1 = I2).
* #I1 [2: #V1 ] * #I2 [2,4: #V2 ]
[1: elim (eq_bind2_dec I1 I2) #HI
    [ elim (eq_term_dec V1 V2) #HV ]
|4: elim (eq_bind1_dec I1 I2) #HI
]
/2 width=1 by or_introl/
@or_intror #H destruct /2 width=1 by/
qed-.
