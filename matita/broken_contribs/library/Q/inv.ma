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

include "Q/q/q.ma".
include "Q/q.ma".
include "Q/fraction/finv.ma".

theorem denominator_integral_factor_finv:
 ∀f. enumerator_integral_fraction f = denominator_integral_fraction (finv f).
 intro;
 elim f;
  [1,2: reflexivity
  |simplify;
   rewrite > H;
   elim z; simplify; reflexivity]
qed.

definition is_positive ≝
 λq.
  match q with
   [ Qpos _ ⇒ True
   | _ ⇒ False
   ].

definition is_negative ≝
 λq.
  match q with
   [ Qneg _ ⇒ True
   | _ ⇒ False
   ].

(*
theorem is_positive_denominator_Qinv:
 ∀q. is_positive q → enumerator q = denominator (Qinv q).
 intro;
 elim q;
  [1,3: elim H;
  | simplify; clear H;
    elim r; simplify;
     [ reflexivity
     | rewrite > denominator_integral_factor_finv;
       reflexivity]]
qed.

theorem is_negative_denominator_Qinv:
 ∀q. is_negative q → enumerator q = -(denominator (Qinv q)).
 intro;
 elim q;
  [1,2: elim H;
  | simplify; clear H;
    elim r; simplify;
     [ reflexivity
     | rewrite > denominator_integral_factor_finv;
       unfold Zopp;
       elim (denominator_integral_fraction (finv f));
       simplify;
        [ reflexivity
        | generalize in match (lt_O_defactorize_aux (nat_fact_of_integral_fraction a) O);
          elim (defactorize_aux (nat_fact_of_integral_fraction a) O);
          simplify;
           [ elim (Not_lt_n_n ? H)
           | reflexivity]]]]
qed.

theorem is_positive_enumerator_Qinv:
  ∀q. is_positive q → enumerator (Qinv q) = denominator q.
 intros;
 lapply (is_positive_denominator_Qinv (Qinv q));
  [ rewrite > Qinv_Qinv in Hletin;
    assumption
  | elim q in H ⊢ %; assumption]
qed.

theorem is_negative_enumerator_Qinv:
  ∀q. is_negative q → enumerator (Qinv q) = -(denominator q).
 intros;
 lapply (is_negative_denominator_Qinv (Qinv q));
  [ rewrite > Qinv_Qinv in Hletin;
    assumption
  | elim q in H ⊢ %; assumption]
qed.
*)