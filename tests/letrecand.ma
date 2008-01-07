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



include "nat/nat.ma".

let rec pari n : Prop :=
 match n with
  [ O ⇒ True
  | S n ⇒ dispari n
  ]
and dispari n : Prop :=
 match n with
  [ O => False
  | S n => pari n
  ].
  
definition pari2 ≝
let rec pari n : Prop :=
 match n with
  [ O ⇒ True
  | S n ⇒ dispari n
  ]
and dispari n : Prop :=
 match n with
  [ O => False
  | S n => pari n
  ]
in pari.

definition dispari2 ≝
let rec pari n : Prop :=
 match n with
  [ O ⇒ True
  | S n ⇒ dispari n
  ]
and dispari n : Prop :=
 match n with
  [ O => False
  | S n => pari n
  ]
in dispari.

lemma test_pari: pari (S (S O)).
simplify.
constructor 1.
qed.

lemma test_pari2: pari2 (S (S O)).
simplify.
constructor 1.
qed.

lemma test_dispari: dispari (S O).
simplify.
constructor 1.
qed.

lemma test_dispari2: dispari2 (S O).
simplify.
constructor 1.
qed.
