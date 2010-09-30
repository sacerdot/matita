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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/bool.ma".

(* ******** *)
(* BOOLEANI *)
(* ******** *)

(*
ndefinition bool_destruct_aux ≝
Πb1,b2:bool.ΠP:Prop.b1 = b2 →
 match eq_bool b1 b2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition bool_destruct : bool_destruct_aux.
 #b1; #b2; #P; #H;
 nrewrite < H;
 nelim b1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma symmetric_eqbool : symmetricT bool bool eq_bool.
 #b1; #b2;
 nelim b1;
 nelim b2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_andbool : symmetricT bool bool and_bool.
 #b1; #b2;
 nelim b1;
 nelim b2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma associative_andbool : ∀b1,b2,b3.((b1 ⊗ b2) ⊗ b3) = (b1 ⊗ (b2 ⊗ b3)).
 #b1; #b2; #b3;
 nelim b1;
 nelim b2;
 nelim b3;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_orbool : symmetricT bool bool or_bool.
 #b1; #b2;
 nelim b1;
 nelim b2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma associative_orbool : ∀b1,b2,b3.((b1 ⊕ b2) ⊕ b3) = (b1 ⊕ (b2 ⊕ b3)).
 #b1; #b2; #b3;
 nelim b1;
 nelim b2;
 nelim b3;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_xorbool : symmetricT bool bool xor_bool.
 #b1; #b2;
 nelim b1;
 nelim b2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma associative_xorbool : ∀b1,b2,b3.((b1 ⊙ b2) ⊙ b3) = (b1 ⊙ (b2 ⊙ b3)).
 #b1; #b2; #b3;
 nelim b1;
 nelim b2;
 nelim b3;
 nnormalize;
 napply refl_eq.
nqed.

nlemma eqbool_to_eq : ∀b1,b2:bool.(eq_bool b1 b2 = true) → (b1 = b2).
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,4: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma eq_to_eqbool : ∀b1,b2.b1 = b2 → eq_bool b1 b2 = true.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,4: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma decidable_bool : ∀x,y:bool.decidable (x = y).
 #x; #y;
 nnormalize;
 nelim x;
 nelim y;
 ##[ ##1,4: napply (or2_intro1 (? = ?) (? ≠ ?) …); napply refl_eq
 ##| ##*: napply (or2_intro2 (? = ?) (? ≠ ?) …);
          nnormalize; #H;
          napply False_ind;
          ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma decidable_bexpr : ∀x.(x = true) ∨ (x = false).
 #x; ncases x;
 ##[ ##1: napply (or2_intro1 (true = true) (true = false) (refl_eq …))
 ##| ##2: napply (or2_intro2 (false = true) (false = false) (refl_eq …))
 ##]
nqed.

nlemma neqbool_to_neq : ∀b1,b2:bool.(eq_bool b1 b2 = false) → (b1 ≠ b2).
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,4: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##*: #H; #H1; ndestruct (*napply (bool_destruct … H1)*)
 ##]
nqed.

nlemma neq_to_neqbool : ∀b1,b2.b1 ≠ b2 → eq_bool b1 b2 = false.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,4: #H; nelim (H (refl_eq …))
 ##| ##*: #H; napply refl_eq
 ##]
nqed.

nlemma eqfalse_to_neqtrue : ∀x.x = false → x ≠ true.
 #x; nelim x;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##2: #H; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
 ##]
nqed.

nlemma eqtrue_to_neqfalse : ∀x.x = true → x ≠ false.
 #x; nelim x;
 ##[ ##1: #H; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
 ##| ##2: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neqfalse_to_eqtrue : ∀x.x ≠ false → x = true.
 #x; nelim x;
 ##[ ##1: #H; napply refl_eq
 ##| ##2: nnormalize; #H; nelim (H (refl_eq …))
 ##]
nqed.

nlemma neqtrue_to_eqfalse : ∀x.x ≠ true → x = false.
 #x; nelim x;
 ##[ ##1: nnormalize; #H; nelim (H (refl_eq …))
 ##| ##2: #H; napply refl_eq
 ##]
nqed.

nlemma andb_true_true_l: ∀b1,b2.(b1 ⊗ b2) = true → b1 = true.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,2: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma andb_true_true_r: ∀b1,b2.(b1 ⊗ b2) = true → b2 = true.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1,3: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma andb_false2
 : ∀b1,b2.(b1 ⊗ b2) = false →
   (b1 = false) ∨ (b2 = false).
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##2,4: #H; napply (or2_intro2 … H)
 ##| ##3: #H; napply (or2_intro1 … H)
 ##]
nqed.

nlemma andb_false3
 : ∀b1,b2,b3.(b1 ⊗ b2 ⊗ b3) = false →
   Or3 (b1 = false) (b2 = false) (b3 = false).
 #b1; #b2; #b3;
 ncases b1;
 ncases b2;
 ncases b3;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##5,6,7,8: #H; napply (or3_intro1 … H)
 ##| ##2,4: #H; napply (or3_intro3 … H)
 ##| ##3: #H; napply (or3_intro2 … H)
 ##]
nqed.

nlemma andb_false4
 : ∀b1,b2,b3,b4.(b1 ⊗ b2 ⊗ b3 ⊗ b4) = false →
   Or4 (b1 = false) (b2 = false) (b3 = false) (b4 = false).
 #b1; #b2; #b3; #b4;
 ncases b1;
 ncases b2;
 ncases b3;
 ncases b4;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##9,10,11,12,13,14,15,16: #H; napply (or4_intro1 … H)
 ##| ##5,6,7,8: #H; napply (or4_intro2 … H)
 ##| ##3,4: #H; napply (or4_intro3 … H)
 ##| ##2: #H; napply (or4_intro4 … H)
 ##]
nqed.

nlemma andb_false5
 : ∀b1,b2,b3,b4,b5.(b1 ⊗ b2 ⊗ b3 ⊗ b4 ⊗ b5) = false →
   Or5 (b1 = false) (b2 = false) (b3 = false) (b4 = false) (b5 = false).
 #b1; #b2; #b3; #b4; #b5;
 ncases b1;
 ncases b2;
 ncases b3;
 ncases b4;
 ncases b5;
 nnormalize;
 ##[ ##1: #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32: #H; napply (or5_intro1 … H)
 ##| ##9,10,11,12,13,14,15,16: #H; napply (or5_intro2 … H)
 ##| ##5,6,7,8: #H; napply (or5_intro3 … H)
 ##| ##3,4: #H; napply (or5_intro4 … H)
 ##| ##2: #H; napply (or5_intro5 … H)
 ##]
nqed.

nlemma andb_false2_1 : ∀b.(false ⊗ b) = false.
 #b; nnormalize; napply refl_eq. nqed.
nlemma andb_false2_2 : ∀b.(b ⊗ false) = false.
 #b; nelim b; nnormalize; napply refl_eq. nqed.

nlemma andb_false3_1 : ∀b1,b2.(false ⊗ b1 ⊗ b2) = false.
 #b1; #b2; nnormalize; napply refl_eq. nqed.
nlemma andb_false3_2 : ∀b1,b2.(b1 ⊗ false ⊗ b2) = false.
 #b1; #b2; nelim b1; nnormalize; napply refl_eq. nqed.
nlemma andb_false3_3 : ∀b1,b2.(b1 ⊗ b2 ⊗ false) = false.
 #b1; #b2; nelim b1; nelim b2; nnormalize; napply refl_eq. nqed.

nlemma andb_false4_1 : ∀b1,b2,b3.(false ⊗ b1 ⊗ b2 ⊗ b3) = false.
 #b1; #b2; #b3; nnormalize; napply refl_eq. nqed.
nlemma andb_false4_2 : ∀b1,b2,b3.(b1 ⊗ false ⊗ b2 ⊗ b3) = false.
 #b1; #b2; #b3; nelim b1; nnormalize; napply refl_eq. nqed.
nlemma andb_false4_3 : ∀b1,b2,b3.(b1 ⊗ b2 ⊗ false ⊗ b3) = false.
 #b1; #b2; #b3; nelim b1; nelim b2; nnormalize; napply refl_eq. nqed.
nlemma andb_false4_4 : ∀b1,b2,b3.(b1 ⊗ b2 ⊗ b3 ⊗ false) = false.
 #b1; #b2; #b3; nelim b1; nelim b2; nelim b3; nnormalize; napply refl_eq. nqed.

nlemma andb_false5_1 : ∀b1,b2,b3,b4.(false ⊗ b1 ⊗ b2 ⊗ b3 ⊗ b4) = false.
 #b1; #b2; #b3; #b4; nnormalize; napply refl_eq. nqed.
nlemma andb_false5_2 : ∀b1,b2,b3,b4.(b1 ⊗ false ⊗ b2 ⊗ b3 ⊗ b4) = false.
 #b1; #b2; #b3; #b4; nelim b1; nnormalize; napply refl_eq. nqed.
nlemma andb_false5_3 : ∀b1,b2,b3,b4.(b1 ⊗ b2 ⊗ false ⊗ b3 ⊗ b4) = false.
 #b1; #b2; #b3; #b4; nelim b1; nelim b2; nnormalize; napply refl_eq. nqed.
nlemma andb_false5_4 : ∀b1,b2,b3,b4.(b1 ⊗ b2 ⊗ b3 ⊗ false ⊗ b4) = false.
 #b1; #b2; #b3; #b4; nelim b1; nelim b2; nelim b3; nnormalize; napply refl_eq. nqed.
nlemma andb_false5_5 : ∀b1,b2,b3,b4.(b1 ⊗ b2 ⊗ b3 ⊗ b4 ⊗ false) = false.
 #b1; #b2; #b3; #b4; nelim b1; nelim b2; nelim b3; nelim b4; nnormalize; napply refl_eq. nqed.

nlemma orb_false_false_l : ∀b1,b2:bool.(b1 ⊕ b2) = false → b1 = false.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##4: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma orb_false_false_r : ∀b1,b2:bool.(b1 ⊕ b2) = false → b2 = false.
 #b1; #b2;
 ncases b1;
 ncases b2;
 nnormalize;
 ##[ ##4: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.
