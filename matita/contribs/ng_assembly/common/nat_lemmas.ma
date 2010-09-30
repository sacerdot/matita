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

include "common/nat.ma".
include "num/bool_lemmas.ma".

(* ******** *)
(* NATURALI *)
(* ******** *)

nlemma nat_destruct_S_S : ∀n1,n2:nat.S n1 = S n2 → n1 = n2.
 #n1; #n2; #H;
 nchange with (match S n2 with [ O ⇒ False | S a ⇒ n1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(* !!! da togliere *)
nlemma nat_destruct_0_S : ∀n:nat.O = S n → False.
 #n; #H;
 nchange with (match S n with [ O ⇒ True | S a ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply I.
nqed.

(* !!! da togliere *)
nlemma nat_destruct_S_0 : ∀n:nat.S n = O → False.
 #n; #H;
 nchange with (match S n with [ O ⇒ True | S a ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

nlemma eq_to_eqnat : ∀n1,n2:nat.n1 = n2 → eq_nat n1 n2 = true.
 #n1;
 nelim n1;
 ##[ ##1: #n2;
          nelim n2;
          nnormalize;
          ##[ ##1: #H; napply refl_eq
          ##| ##2: #n3; #H; #H1; ndestruct (*nelim (nat_destruct_0_S ? H1)*)
          ##]
 ##| ##2: #n2; #H; #n3; #H1;
          ncases n3 in H1:(%) ⊢ %;
          nnormalize;
          ##[ ##1: #H1; ndestruct (*nelim (nat_destruct_S_0 ? H1)*)
          ##| ##2: #n4; #H1;
                   napply (H n4 (nat_destruct_S_S … H1))
          ##]
 ##]
nqed.

nlemma neqnat_to_neq : ∀n1,n2:nat.(eq_nat n1 n2 = false → n1 ≠ n2).
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_nat n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqnat n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqnat_to_eq : ∀n1,n2:nat.(eq_nat n1 n2 = true → n1 = n2).
 #n1;
 nelim n1;
 ##[ ##1: #n2;
          nelim n2;
          nnormalize;
          ##[ ##1: #H; napply refl_eq
          ##| ##2: #n3; #H; #H1; ndestruct (*napply (bool_destruct … (O = S n3) H1)*)
          ##]
 ##| ##2: #n2; #H; #n3; #H1;
          ncases n3 in H1:(%) ⊢ %;
          nnormalize;
          ##[ ##1: #H1; ndestruct (*napply (bool_destruct … (S n2 = O) H1)*)
          ##| ##2: #n4; #H1;
                   nrewrite > (H n4 H1);
                   napply refl_eq
          ##]
 ##]
nqed.

nlemma neq_to_neqnat : ∀n1,n2:nat.n1 ≠ n2 → eq_nat n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_nat n1 n2));
 napply (not_to_not (eq_nat n1 n2 = true) (n1 = n2) ? H);
 napply (eqnat_to_eq n1 n2).
nqed.

nlemma decidable_nat : ∀x,y:nat.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_nat x y = true) (eq_nat x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqnat_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqnat_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqnat : symmetricT nat bool eq_nat.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_nat n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqnat n1 n2 H);
          napply (symmetric_eq ? (eq_nat n2 n1) false);
          napply (neq_to_neqnat n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma Sn_p_n_to_S_npn : ∀n1,n2.(S n1) + n2 = S (n1 + n2).
 #n1;
 nelim n1;
 ##[ ##1: nnormalize; #n2; napply refl_eq
 ##| ##2: #n; #H; #n2; nrewrite > (H n2);
          ncases n in H:(%) ⊢ %;
          ##[ ##1: nnormalize; #H; napply refl_eq
          ##| ##2: #n3; nnormalize; #H; napply refl_eq
          ##]
 ##]
nqed.

nlemma n_p_Sn_to_S_npn : ∀n1,n2.n1 + (S n2) = S (n1 + n2).
 #n1;
 nelim n1;
 ##[ ##1: nnormalize; #n2; napply refl_eq
 ##| ##2: #n; #H; #n2;
          nrewrite > (Sn_p_n_to_S_npn n (S n2));
          nrewrite > (H n2);
          napply refl_eq
 ##]
nqed.

nlemma Opn_to_n : ∀n.O + n = n.
 #n; nnormalize; napply refl_eq.
nqed.

nlemma npO_to_n : ∀n.n + O = n.
 #n;
 nelim n;
 ##[ ##1: nnormalize; napply refl_eq
 ##| ##2: #n1; #H;
          nrewrite > (Sn_p_n_to_S_npn n1 O); 
          nrewrite > H;
          napply refl_eq
 ##]
nqed.

nlemma symmetric_plusnat : symmetricT nat nat plus.
 #n1;
 nelim n1;
 ##[ ##1: #n2; nrewrite > (npO_to_n n2); nnormalize; napply refl_eq
 ##| ##2: #n2; #H; #n3;
          nrewrite > (Sn_p_n_to_S_npn n2 n3);
          nrewrite > (n_p_Sn_to_S_npn n3 n2);
          nrewrite > (H n3);
          napply refl_eq
 ##]
nqed.
