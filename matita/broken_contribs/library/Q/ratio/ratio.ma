(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "Q/fraction/fraction.ma".

inductive ratio : Set \def
      one :  ratio
    | frac : fraction \to ratio.

definition unfrac \def \lambda f.
match f with
  [one \Rightarrow pp O
  |frac f \Rightarrow f
  ]
.

lemma injective_frac: injective fraction ratio frac.
unfold.intros.
change with ((unfrac (frac x)) = (unfrac (frac y))).
rewrite < H.reflexivity.
qed.
