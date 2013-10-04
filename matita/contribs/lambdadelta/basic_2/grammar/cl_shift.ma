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

include "basic_2/grammar/lenv_append.ma".

(* SHIFT OF A CLOSURE *******************************************************)

let rec shift L T on L ≝ match L with
[ LAtom       ⇒ T
| LPair L I V ⇒ shift L (-ⓑ{I} V. T)
].

interpretation "shift (closure)" 'Append L T = (shift L T).

(* Basic properties *********************************************************)

lemma shift_append_assoc: ∀L,K. ∀T:term. (L @@ K) @@ T = L @@ K @@ T.
#L #K elim K -K // normalize //
qed.

(* Basic inversion lemmas ***************************************************)

lemma shift_inj: ∀L1,L2. ∀T1,T2:term. L1 @@ T1 = L2 @@ T2 → |L1| = |L2| →
                 L1 = L2 ∧ T1 = T2.
#L1 elim L1 -L1
[ * normalize /2 width=1/
  #L2 #I2 #V2 #T1 #T2 #_ <plus_n_Sm #H destruct
| #L1 #H1 #V1 #IH * normalize
  [ #T1 #T2 #_ <plus_n_Sm #H destruct
  | #L2 #I2 #V2 #T1 #T2 #H1 #H2
    elim (IH … H1) -IH -H1 /2 width=1/ -H2 #H1 #H2 destruct /2 width=1/
  ]
]
qed-.
