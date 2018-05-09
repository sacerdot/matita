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

include "basic_2/notation/constructors/star_0.ma".
include "basic_2/notation/constructors/dxbind2_3.ma".
include "basic_2/notation/constructors/dxabbr_2.ma".
include "basic_2/notation/constructors/dxabst_2.ma".
include "basic_2/syntax/term.ma".

(* GLOBAL ENVIRONMENTS ******************************************************)

(* global environments *)
inductive genv: Type[0] ≝
| GAtom: genv                       (* empty *)
| GPair: genv → bind2 → term → genv (* binary binding construction *)
.

interpretation "sort (global environment)"
   'Star = (GAtom).

interpretation "global environment binding construction (binary)"
   'DxBind2 G I T = (GPair G I T).

interpretation "abbreviation (global environment)"
   'DxAbbr G T = (GPair G Abbr T).

interpretation "abstraction (global environment)"
   'DxAbst G T = (GPair G Abst T).

(* Basic properties *********************************************************)

lemma eq_genv_dec: ∀G1,G2:genv. Decidable (G1 = G2).
#G1 elim G1 -G1 [| #G1 #I1 #T1 #IHG1 ] * [2,4: #G2 #I2 #T2 ]
[3: /2 width=1 by or_introl/
|2: elim (eq_bind2_dec I1 I2) #HI
    [ elim (IHG1 G2) -IHG1 #HG 
      [ elim (eq_term_dec T1 T2) #HT /2 width=1 by or_introl/ ]
    ]
]
@or_intror #H destruct /2 width=1 by/
qed-.
