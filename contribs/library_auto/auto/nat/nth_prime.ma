(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/nat/nth_prime".

include "auto/nat/primes.ma".
include "auto/nat/lt_arith.ma".

(* upper bound by Bertrand's conjecture. *)
(* Too difficult to prove.        
let rec nth_prime n \def
match n with
  [ O \Rightarrow (S(S O))
  | (S p) \Rightarrow
    let previous_prime \def S (nth_prime p) in
    min_aux previous_prime ((S(S O))*previous_prime) primeb].

theorem example8 : nth_prime (S(S O)) = (S(S(S(S(S O))))).
normalize.reflexivity.
qed.

theorem example9 : nth_prime (S(S(S O))) = (S(S(S(S(S(S(S O))))))).
normalize.reflexivity.
qed.

theorem example10 : nth_prime (S(S(S(S O)))) = (S(S(S(S(S(S(S(S(S(S(S O))))))))))).
normalize.reflexivity.
qed. *)

theorem smallest_factor_fact: \forall n:nat.
n < smallest_factor (S n!).
intros.
apply not_le_to_lt.
unfold Not.
intro.
apply (not_divides_S_fact n (smallest_factor(S n!)))
[ apply lt_SO_smallest_factor.
  unfold lt.autobatch
  (*apply le_S_S.
  apply le_SO_fact*)
| assumption
| autobatch
  (*apply divides_smallest_factor_n.
  unfold lt.
  apply le_S_S.
  apply le_O_n*)
]
qed.

theorem ex_prime: \forall n. (S O) \le n \to \exists m.
n < m \land m \le S n! \land (prime m).
intros.
elim H
[ apply (ex_intro nat ? (S(S O))).
  split;autobatch
  (*[ split
    [ apply (le_n (S(S O)))
    | apply (le_n (S(S O)))
    ]
  | apply (primeb_to_Prop (S(S O)))
  ]*)
| apply (ex_intro nat ? (smallest_factor (S (S n1)!))).
  split
  [ autobatch
    (*split
    [ apply smallest_factor_fact
    | apply le_smallest_factor_n
    ]*)
  | (* Andrea: ancora hint non lo trova *)
    apply prime_smallest_factor_n.
    unfold lt.autobatch
    (*apply le_S.
    apply le_SSO_fact.
    unfold lt.
    apply le_S_S.
    assumption*)
  ]
]
qed.

let rec nth_prime n \def
match n with
  [ O \Rightarrow (S(S O))
  | (S p) \Rightarrow
    let previous_prime \def (nth_prime p) in
    let upper_bound \def S previous_prime! in
    min_aux (upper_bound - (S previous_prime)) upper_bound primeb].
    
(* it works, but nth_prime 4 takes already a few minutes -
it must compute factorial of 7 ...*)
(*
theorem example11 : nth_prime (S(S O)) = (S(S(S(S(S O))))).
autobatch.
(*normalize.reflexivity.*)
qed.

theorem example12: nth_prime (S(S(S O))) = (S(S(S(S(S(S(S O))))))).
autobatch.
(*normalize.reflexivity.*)
qed.

theorem example13 : nth_prime (S(S(S(S O)))) = (S(S(S(S(S(S(S(S(S(S(S O))))))))))).
autobatch.
(*normalize.reflexivity.*)
qed.
*)
(*
theorem example14 : nth_prime (S(S(S(S(S O))))) = (S(S(S(S(S(S(S(S(S(S(S O))))))))))).
normalize.reflexivity.
*) 

theorem prime_nth_prime : \forall n:nat.prime (nth_prime n).
intro.
apply (nat_case n)
[ autobatch 
  (*simplify.
  apply (primeb_to_Prop (S(S O)))*)
| intro.
  change with
  (let previous_prime \def (nth_prime m) in
  let upper_bound \def S previous_prime! in
  prime (min_aux (upper_bound - (S previous_prime)) upper_bound primeb)).
  apply primeb_true_to_prime.
  apply f_min_aux_true.
  apply (ex_intro nat ? (smallest_factor (S (nth_prime m)!))).
  split
  [ split
    [ cut (S (nth_prime m)!-(S (nth_prime m)! - (S (nth_prime m))) = (S (nth_prime m)))
      [ rewrite > Hcut.
        exact (smallest_factor_fact (nth_prime m))
      | (* maybe we could factorize this proof *)
        apply plus_to_minus.
        autobatch
        (*apply plus_minus_m_m.
        apply le_S_S.
        apply le_n_fact_n*)
      ]
    | apply le_smallest_factor_n
    ]
  | apply prime_to_primeb_true.
    apply prime_smallest_factor_n.
    unfold lt.autobatch
    (*apply le_S_S.
    apply le_SO_fact*)
  ]
]
qed.

(* properties of nth_prime *)
theorem increasing_nth_prime: increasing nth_prime.
unfold increasing.
intros.
change with
(let previous_prime \def (nth_prime n) in
let upper_bound \def S previous_prime! in
(S previous_prime) \le min_aux (upper_bound - (S previous_prime)) upper_bound primeb).
intros.
cut (upper_bound - (upper_bound -(S previous_prime)) = (S previous_prime))
[ rewrite < Hcut in \vdash (? % ?).
  apply le_min_aux
| apply plus_to_minus.
  autobatch
  (*apply plus_minus_m_m.
  apply le_S_S.
  apply le_n_fact_n*)
]
qed.

variant lt_nth_prime_n_nth_prime_Sn :\forall n:nat. 
(nth_prime n) < (nth_prime (S n)) \def increasing_nth_prime.

theorem injective_nth_prime: injective nat nat nth_prime.
autobatch.
(*apply increasing_to_injective.
apply increasing_nth_prime.*)
qed.

theorem lt_SO_nth_prime_n : \forall n:nat. (S O) \lt nth_prime n.
intros.
(*usando la tattica autobatch qui, dopo svariati minuti la computazione non era
 * ancora terminata
 *)
elim n
[ unfold lt.autobatch
  (*apply le_n*)
| autobatch
  (*apply (trans_lt ? (nth_prime n1))
  [ assumption
  | apply lt_nth_prime_n_nth_prime_Sn
  ]*)
]
qed.

theorem lt_O_nth_prime_n : \forall n:nat. O \lt nth_prime n.
intros.
autobatch.
(*apply (trans_lt O (S O))
[ unfold lt.
  apply le_n
| apply lt_SO_nth_prime_n
]*)
qed.

theorem ex_m_le_n_nth_prime_m: 
\forall n: nat. nth_prime O \le n \to 
\exists m. nth_prime m \le n \land n < nth_prime (S m).
autobatch.
(*intros.
apply increasing_to_le2
[ exact lt_nth_prime_n_nth_prime_Sn
| assumption
]*)
qed.

theorem lt_nth_prime_to_not_prime: \forall n,m. nth_prime n < m \to m < nth_prime (S n) 
\to \lnot (prime m).
intros.
apply primeb_false_to_not_prime.
letin previous_prime \def (nth_prime n).
letin upper_bound \def (S previous_prime!).
apply (lt_min_aux_to_false primeb upper_bound (upper_bound - (S previous_prime)) m)
[ cut (S (nth_prime n)!-(S (nth_prime n)! - (S (nth_prime n))) = (S (nth_prime n)))
  [ rewrite > Hcut.
    assumption
  | apply plus_to_minus.
    autobatch
    (*apply plus_minus_m_m.
    apply le_S_S.
    apply le_n_fact_n*)
  ]
| assumption
]
qed.

(* nth_prime enumerates all primes *)
theorem prime_to_nth_prime : \forall p:nat. prime p \to
\exists i. nth_prime i = p.
intros.
cut (\exists m. nth_prime m \le p \land p < nth_prime (S m))
[ elim Hcut.
  elim H1.
  cut (nth_prime a < p \lor nth_prime a = p)
  [ elim Hcut1
    [ absurd (prime p)
      [ assumption
      | autobatch
        (*apply (lt_nth_prime_to_not_prime a);assumption*)
      ]
    | autobatch
      (*apply (ex_intro nat ? a).
      assumption*)
    ]
  | autobatch
    (*apply le_to_or_lt_eq.
    assumption*)
  ]
| apply ex_m_le_n_nth_prime_m.
  simplify.
  unfold prime in H.
  elim H.
  assumption
]
qed.

