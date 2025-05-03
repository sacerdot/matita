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

include "ground/arith/nat_le.ma".
include "ground/notation/functions/two_0.ma".
include "static_2/notation/functions/omega_0.ma".

(* APPLICABILITY CONDITION **************************************************)

(* applicability condition specification *)
record ac: Type[0] ≝ {
(* applicability domain *)
   ad: predicate nat
}.

(* applicability condition postulates *)
record ac_props (a): Prop ≝ {
   ac_dec: ∀m. Decidable (∃∃n. ad a n & m ≤ n)
}.

(* Notable specifications ***************************************************)

definition apply_top: predicate nat ≝ λn. ⊤.

definition ac_top: ac ≝ mk_ac apply_top.

interpretation "any number (applicability domain)"
  'Omega = (ac_top).

lemma ac_top_props: ac_props ac_top ≝ mk_ac_props ….
/3 width=3 by or_introl, ex2_intro/
qed.

definition ac_eq (k): ac ≝ mk_ac (eq … k).

(* Note: we denote "❴𝟏❵", that is "❴𝟎,𝟏❵", with "𝟐" *)
interpretation "one (applicability domain)"
  'Two = (ac_eq (npos punit)).

(* Note: we denote "❴𝟎❵" with "𝟏" *)
interpretation "zero (applicability domain)"
  'One = (ac_eq nzero).

lemma ac_eq_props (k): ac_props (ac_eq k) ≝ mk_ac_props ….
#m elim (nle_dec m k) #Hm
[ /3 width=3 by or_introl, ex2_intro/
| @or_intror * #n #Hn #Hmn destruct /2 width=1 by/
]
qed.

definition ac_le (k): ac ≝ mk_ac (λn. n ≤ k).

lemma ac_le_props (k): ac_props (ac_le k) ≝ mk_ac_props ….
#m elim (nle_dec m k) #Hm
[ /3 width=3 by or_introl, ex2_intro/
| @or_intror * #n #Hn #Hmn
  /3 width=3 by nle_trans/
]
qed.
