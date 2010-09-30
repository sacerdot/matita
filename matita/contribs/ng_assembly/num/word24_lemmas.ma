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

include "num/byte8_lemmas.ma".
include "num/word24.ma".

(* **** *)
(* BYTE *)
(* **** *)

nlemma word24_destruct_1 :
∀x1,x2,y1,y2,z1,z2.
 mk_word24 x1 y1 z1 = mk_word24 x2 y2 z2 → x1 = x2.
 #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match mk_word24 x2 y2 z2 with [ mk_word24 a _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma word24_destruct_2 :
∀x1,x2,y1,y2,z1,z2.
 mk_word24 x1 y1 z1 = mk_word24 x2 y2 z2 → y1 = y2.
 #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match mk_word24 x2 y2 z2 with [ mk_word24 _ a _ ⇒ y1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma word24_destruct_3 :
∀x1,x2,y1,y2,z1,z2.
 mk_word24 x1 y1 z1 = mk_word24 x2 y2 z2 → z1 = z2.
 #x1; #x2; #y1; #y2; #z1; #z2; #H;
 nchange with (match mk_word24 x2 y2 z2 with [ mk_word24 _ _ a ⇒ z1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqw24 : symmetricT word24 bool eq_w24.
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 nchange with (((eq_b8 e1 e4)⊗(eq_b8 e2 e5)⊗(eq_b8 e3 e6)) = ((eq_b8 e4 e1)⊗(eq_b8 e5 e2)⊗(eq_b8 e6 e3)));
 nrewrite > (symmetric_eqb8 e1 e4);
 nrewrite > (symmetric_eqb8 e2 e5);
 nrewrite > (symmetric_eqb8 e3 e6);
 napply refl_eq.
nqed.

nlemma eqw24_to_eq : ∀b1,b2.(eq_w24 b1 b2 = true) → (b1 = b2).
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 nchange in ⊢ (% → ?) with (((eq_b8 e1 e4)⊗(eq_b8 e2 e5)⊗(eq_b8 e3 e6)) = true);
 #H;
 nrewrite < (eqb8_to_eq … (andb_true_true_r … H));
 nrewrite < (eqb8_to_eq … (andb_true_true_r … (andb_true_true_l … H)));
 nrewrite < (eqb8_to_eq … (andb_true_true_l … (andb_true_true_l … H)));
 napply refl_eq.
nqed.

nlemma eq_to_eqw24 : ∀b1,b2.(b1 = b2) → (eq_w24 b1 b2 = true).
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 #H;
 nchange with (((eq_b8 e1 e4)⊗(eq_b8 e2 e5)⊗(eq_b8 e3 e6)) = true);
 nrewrite < (word24_destruct_1 … H);
 nrewrite < (word24_destruct_2 … H);
 nrewrite < (word24_destruct_3 … H);
 nrewrite > (eq_to_eqb8 e1 e1 (refl_eq …));
 nrewrite > (eq_to_eqb8 e2 e2 (refl_eq …)); 
 nrewrite > (eq_to_eqb8 e3 e3 (refl_eq …)); 
 nnormalize;
 napply refl_eq.
nqed.

nlemma decidable_w24_aux1 :
∀e1,e2,e3,e4,e5,e6.e1 ≠ e4 → (mk_word24 e1 e2 e3) ≠ (mk_word24 e4 e5 e6).
 #e1; #e2; #e3; #e4; #e5; #e6;
 nnormalize; #H; #H1;
 napply (H (word24_destruct_1 … H1)).
nqed.

nlemma decidable_w24_aux2 :
∀e1,e2,e3,e4,e5,e6.e2 ≠ e5 → (mk_word24 e1 e2 e3) ≠ (mk_word24 e4 e5 e6).
 #e1; #e2; #e3; #e4; #e5; #e6;
 nnormalize; #H; #H1;
 napply (H (word24_destruct_2 … H1)).
nqed.

nlemma decidable_w24_aux3 :
∀e1,e2,e3,e4,e5,e6.e3 ≠ e6 → (mk_word24 e1 e2 e3) ≠ (mk_word24 e4 e5 e6).
 #e1; #e2; #e3; #e4; #e5; #e6;
 nnormalize; #H; #H1;
 napply (H (word24_destruct_3 … H1)).
nqed.

nlemma decidable_w24 : ∀b1,b2:word24.(decidable (b1 = b2)).
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 nnormalize;
 napply (or2_elim (e1 = e4) (e1 ≠ e4) ? (decidable_b8 e1 e4) …);
 ##[ ##2: #H; napply (or2_intro2 … (decidable_w24_aux1 e1 e2 e3 e4 e5 e6 H))
 ##| ##1: #H; napply (or2_elim (e2 = e5) (e2 ≠ e5) ? (decidable_b8 e2 e5) …);
          ##[ ##2: #H1; napply (or2_intro2 … (decidable_w24_aux2 e1 e2 e3 e4 e5 e6 H1))
          ##| ##1: #H1; napply (or2_elim (e3 = e6) (e3 ≠ e6) ? (decidable_b8 e3 e6) …);
                   ##[ ##2: #H2; napply (or2_intro2 … (decidable_w24_aux3 e1 e2 e3 e4 e5 e6 H2))
                   ##| ##1: #H2; nrewrite > H; nrewrite > H1; nrewrite > H2;
                                 napply (or2_intro1 … (refl_eq ? (mk_word24 e4 e5 e6)))
                   ##]
          ##]
 ##]
nqed.

nlemma neqw24_to_neq : ∀b1,b2.(eq_w24 b1 b2 = false) → (b1 ≠ b2).
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 #H;
 nchange in H:(%) with (((eq_b8 e1 e4)⊗(eq_b8 e2 e5)⊗(eq_b8 e3 e6)) = false);
 #H1;
 nrewrite > (word24_destruct_1 … H1) in H:(%);
 nrewrite > (word24_destruct_2 … H1);
 nrewrite > (word24_destruct_3 … H1);
 nrewrite > (eq_to_eqb8 e4 e4 (refl_eq …));
 nrewrite > (eq_to_eqb8 e5 e5 (refl_eq …));
 nrewrite > (eq_to_eqb8 e6 e6 (refl_eq …));
 #H; ndestruct.
nqed.

nlemma word24_destruct :
∀e1,e2,e3,e4,e5,e6.
 ((mk_word24 e1 e2 e3) ≠ (mk_word24 e4 e5 e6)) →
 (Or3 (e1 ≠ e4) (e2 ≠ e5) (e3 ≠ e6)).
 #e1; #e2; #e3; #e4; #e5; #e6;
 nnormalize; #H;
 napply (or2_elim (e1 = e4) (e1 ≠ e4) ? (decidable_b8 e1 e4) …);
 ##[ ##2: #H1; napply (or3_intro1 … H1)
 ##| ##1: #H1; napply (or2_elim (e2 = e5) (e2 ≠ e5) ? (decidable_b8 e2 e5) …);
          ##[ ##2: #H2; napply (or3_intro2 … H2)
          ##| ##1: #H2; napply (or2_elim (e3 = e6) (e3 ≠ e6) ? (decidable_b8 e3 e6) …);
                   ##[ ##2: #H3; napply (or3_intro3 … H3)
                   ##| ##1: #H3; nrewrite > H1 in H:(%);
                            nrewrite > H2; nrewrite > H3;
                            #H; nelim (H (refl_eq …))
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_neqw24 : ∀b1,b2.((b1 ≠ b2) → (eq_w24 b1 b2 = false)).
 #b1; nelim b1; #e1; #e2; #e3;
 #b2; nelim b2; #e4; #e5; #e6;
 #H; nchange with (((eq_b8 e1 e4)⊗(eq_b8 e2 e5)⊗(eq_b8 e3 e6)) = false);
 napply (or3_elim (e1 ≠ e4) (e2 ≠ e5) (e3 ≠ e6) ? (word24_destruct e1 e2 e3 e4 e5 e6 … H) …);
 ##[ ##1: #H1; nrewrite > (neq_to_neqb8 e1 e4 H1); nnormalize; napply refl_eq
 ##| ##2: #H1; nrewrite > (neq_to_neqb8 e2 e5 H1);
          nrewrite > (symmetric_andbool (eq_b8 e1 e4) …);
          nnormalize; napply refl_eq
 ##| ##3: #H1; nrewrite > (neq_to_neqb8 e3 e6 H1);
          nrewrite > (symmetric_andbool ((eq_b8 e1 e4)⊗(eq_b8 e2 e5)) …);
          nnormalize; napply refl_eq
 ##]
nqed.
