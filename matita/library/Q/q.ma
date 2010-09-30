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

include "Z/compare.ma".
include "Z/plus.ma".
include "nat/factorization.ma".
include "Q/fraction/fraction.ma".

let rec enumerator_integral_fraction l ≝
 match l with
  [ pp n ⇒ Some ? l
  | nn _ ⇒ None ?
  | cons z r ⇒
     match enumerator_integral_fraction r with
      [ None ⇒
         match z with
          [ pos n ⇒ Some ? (pp n)
          | _ ⇒ None ?
          ]
      | Some r' ⇒
         Some ?
          match z with
           [ neg _ ⇒ cons OZ r'
           | _ ⇒ cons z r'
           ]
       ]
  ].

let rec denominator_integral_fraction l ≝
 match l with
  [ pp _ ⇒ None ?
  | nn n ⇒ Some ? (pp n)
  | cons z r ⇒
     match denominator_integral_fraction r with
      [ None ⇒
         match z with
          [ neg n ⇒ Some ? (pp n)
          | _ ⇒ None ?
          ]
      | Some r' ⇒
         Some ?
          match z with
           [ pos _ ⇒ cons OZ r'
           | neg m ⇒ cons (pos m) r'
           | OZ ⇒ cons OZ r'
           ]
       ]
  ].

(*
definition enumerator_of_fraction ≝
 λq.
  match q with
   [ one ⇒ S O
   | frac f ⇒
      match enumerator_integral_fraction f with
       [ None ⇒ S O
       | Some l ⇒ defactorize_aux (nat_fact_of_integral_fraction l) O
       ]
   ].

definition denominator_of_fraction ≝
 λq.
  match q with
   [ one ⇒ S O
   | frac f ⇒
      match denominator_integral_fraction f with
       [ None ⇒ S O
       | Some l ⇒ defactorize_aux (nat_fact_of_integral_fraction l) O
       ]
   ].

definition enumerator ≝
 λq.
  match q with
   [ OQ ⇒ OZ
   | Qpos r ⇒ (enumerator_of_fraction r : Z)
   | Qneg r ⇒ neg(pred (enumerator_of_fraction r))
   ].

definition denominator ≝
 λq.
  match q with
   [ OQ ⇒ S O
   | Qpos r ⇒ denominator_of_fraction r
   | Qneg r ⇒ denominator_of_fraction r
   ].
*)