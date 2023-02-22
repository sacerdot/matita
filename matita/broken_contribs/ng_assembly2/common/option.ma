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

include "common/comp.ma".
include "common/option_base.ma".
include "num/bool_lemmas.ma".

(* ****** *)
(* OPTION *)
(* ****** *)

nlemma option_destruct_some_some : ∀T.∀x1,x2:T.Some T x1 = Some T x2 → x1 = x2.
 #T; #x1; #x2; #H;
 nchange with (match Some T x2 with [ None ⇒ False | Some a ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma option_destruct_some_none : ∀T.∀x:T.Some T x = None T → False.
 #T; #x; #H;
 nchange with (match Some T x with [ None ⇒ True | Some a ⇒ False ]);
 nrewrite > H;
 nnormalize;
 napply I.
nqed.

nlemma option_destruct_none_some : ∀T.∀x:T.None T = Some T x → False.
 #T; #x; #H;
 nchange with (match Some T x with [ None ⇒ True | Some a ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply I.
nqed.

nlemma symmetric_eqoption :
∀T:Type.∀f:T → T → bool.
 (symmetricT T bool f) →
 (∀op1,op2:option T.
  (eq_option T f op1 op2 = eq_option T f op2 op1)).
 #T; #f; #H;
 #op1; #op2; nelim op1; nelim op2;
 nnormalize;
 ##[ ##1: napply refl_eq
 ##| ##2,3: #H; napply refl_eq
 ##| ##4: #a; #a0;
          nrewrite > (H a0 a);
          napply refl_eq
 ##]
nqed.

nlemma eq_to_eqoption :
∀T.∀f:T → T → bool.
 (∀x1,x2:T.x1 = x2 → f x1 x2 = true) →
 (∀op1,op2:option T.
  (op1 = op2 → eq_option T f op1 op2 = true)).
 #T; #f; #H;
 #op1; #op2; nelim op1; nelim op2;
 nnormalize;
 ##[ ##1: #H1; napply refl_eq
 ##| ##2: #a; #H1;
         (* !!! ndestruct: assert false *)
         nelim (option_destruct_none_some ?? H1)
 ##| ##3: #a; #H1;
          (* !!! ndestruct: assert false *)
          nelim (option_destruct_some_none ?? H1)
 ##| ##4: #a; #a0; #H1;
          nrewrite > (H … (option_destruct_some_some … H1));
          napply refl_eq
 ##]
nqed.

nlemma eqoption_to_eq :
∀T.∀f:T → T → bool.
 (∀x1,x2:T.f x1 x2 = true → x1 = x2) →
 (∀op1,op2:option T.
  (eq_option T f op1 op2 = true → op1 = op2)).
 #T; #f; #H;
 #op1; #op2; nelim op1; nelim op2;
 nnormalize;
 ##[ ##1: #H1; napply refl_eq
 ##| ##2,3: #a; #H1; ndestruct (*napply (bool_destruct … H1)*)
 ##| ##4: #a; #a0; #H1;
          nrewrite > (H … H1);
          napply refl_eq
 ##]
nqed.

nlemma decidable_option :
∀T.(Πx,y:T.decidable (x = y)) →
   (∀x,y:option T.decidable (x = y)).
 #T; #H; #x; nelim x;
 ##[ ##1: #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro1 (? = ?) (? ≠ ?) (refl_eq …))
          ##| ##2: #yy; nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H1;
                   (* !!! ndestruct: assert false *)
                   napply (option_destruct_none_some T … H1)
          ##]
 ##| ##2: #xx; #y; ncases y;
          ##[ ##1: nnormalize; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                   nnormalize; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (option_destruct_some_none T … H2)
          ##| ##2: #yy; nnormalize; napply (or2_elim (xx = yy) (xx ≠ yy) ? (H …));
                   ##[ ##2: #H1; napply (or2_intro2 (? = ?) (? ≠ ?) ?);
                            nnormalize; #H2;
                            napply (H1 (option_destruct_some_some T … H2))
                   ##| ##1: #H1; napply (or2_intro1 (? = ?) (? ≠ ?) ?);
                            nrewrite > H1; napply refl_eq
                   ##]
          ##]
 ##]
nqed.

nlemma neq_to_neqoption :
∀T.∀f:T → T → bool.
 (∀x1,x2:T.x1 ≠ x2 → f x1 x2 = false) →
 (∀op1,op2:option T.
  (op1 ≠ op2 → eq_option T f op1 op2 = false)).
 #T; #f; #H; #op1; nelim op1;
 ##[ ##1: #op2; ncases op2;
          ##[ ##1: nnormalize; #H1; nelim (H1 (refl_eq …))
          ##| ##2: #yy; nnormalize; #H1; napply refl_eq
          ##]
 ##| ##2: #xx; #op2; ncases op2;
          ##[ ##1: nnormalize; #H1; napply refl_eq
          ##| ##2: #yy; nnormalize; #H1; napply (H xx yy …);
                   nnormalize; #H2; nrewrite > H2 in H1:(%); #H1;
                   napply (H1 (refl_eq …))
          ##]
 ##]
nqed.

nlemma neqoption_to_neq :
∀T.∀f:T → T → bool.
 (∀x1,x2:T.f x1 x2 = false → x1 ≠ x2) →
 (∀op1,op2:option T.
  (eq_option T f op1 op2 = false → op1 ≠ op2)).
 #T; #f; #H; #op1; nelim op1;
 ##[ ##1: #op2; ncases op2;
          ##[ ##1: nnormalize; #H1;
                   ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #yy; nnormalize; #H1; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (option_destruct_none_some T … H2)
          ##]
 ##| ##2: #xx; #op2; ncases op2;
          ##[ ##1: nnormalize; #H1; #H2;
                   (* !!! ndestruct: assert false *)
                   napply (option_destruct_some_none T … H2)
          ##| ##2: #yy; nnormalize; #H1; #H2; napply (H xx yy H1 ?);
                   napply (option_destruct_some_some T … H2)
          ##]
 ##]
nqed.

nlemma option_is_comparable :
 comparable → comparable.
 #T; napply (mk_comparable (option T));
 ##[ napply (None ?)
 ##| napply (λx.false)
 ##| napply (eq_option … (eqc T))
 ##| napply (eqoption_to_eq … (eqc T));
     napply (eqc_to_eq T)
 ##| napply (eq_to_eqoption … (eqc T));
     napply (eq_to_eqc T)
 ##| napply (neqoption_to_neq … (eqc T));
     napply (neqc_to_neq T)
 ##| napply (neq_to_neqoption … (eqc T));
     napply (neq_to_neqc T)
 ##| napply decidable_option;
     napply (decidable_c T)
 ##| napply symmetric_eqoption;
     napply (symmetric_eqc T)
 ##]
nqed.

unification hint 0 ≔ S: comparable;
         T ≟ (carr S),
         X ≟ (option_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ option T.
