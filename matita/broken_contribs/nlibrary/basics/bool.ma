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

include "basics/eq.ma".
include "basics/functions.ma".

ninductive bool: Type ≝ 
  | true : bool
  | false : bool.

(*
ntheorem bool_elim: \forall P:bool \to Prop. \forall b:bool.
  (b = true \to P true)
  \to (b = false \to P false)
  \to P b.
  intros 2 (P b).
  elim b;
  [ apply H; reflexivity
  | apply H1; reflexivity
  ]
qed.*)

(* ndestrcut does not work *)
ntheorem not_eq_true_false : true \neq false.
napply nmk; #Heq;
nchange with match true with [true ⇒ False|false ⇒ True];
nrewrite > Heq; //; nqed.

ndefinition notb : bool → bool ≝
\lambda b:bool. match b with 
 [true ⇒ false
 |false ⇒ true ].

interpretation "boolean not" 'not x = (notb x).

ntheorem notb_elim: ∀ b:bool.∀ P:bool → Prop.
match b with
[ true ⇒ P false
| false ⇒ P true] → P (notb b).
#b; #P; nelim b; nnormalize; //; nqed.

ntheorem notb_notb: ∀b:bool. notb (notb b) = b.
#b; nelim b; //; nqed.

ntheorem injective_notb: injective bool bool notb.
#b1; #b2; #H; //; nqed.

ndefinition andb : bool → bool → bool ≝
\lambda b1,b2:bool. match b1 with 
 [ true ⇒ b2
 | false ⇒ false ].

interpretation "boolean and" 'and x y = (andb x y).

ntheorem andb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with
 [ true ⇒ P b2
 | false ⇒ P false] → P (b1 ∧ b2).
#b1; #b2; #P; nelim b1; nnormalize; //; nqed.

(*
ntheorem and_true: ∀ a,b:bool. 
andb a b =true → a =true ∧ b= true.
#a; #b; ncases a; nnormalize;#H;napply conj;//;
  [split
    [reflexivity|assumption]
  |apply False_ind.
   apply not_eq_true_false.
   apply sym_eq.
   assumption
  ]
qed. *)

ntheorem andb_true_l: ∀ b1,b2. (b1 ∧ b2) = true → b1 = true.
#b1; ncases b1; nnormalize; //; nqed.

ntheorem andb_true_r: \forall b1,b2. (b1 ∧ b2) = true → b2 = true.
#b1; ncases b1; nnormalize; //; 
#b2; ncases b2; //; nqed.

ndefinition orb : bool → bool → bool ≝
λ b1,b2:bool. 
 match b1 with 
 [ true ⇒ true
 | false ⇒ b2].
 
interpretation "boolean or" 'or x y = (orb x y).

ntheorem orb_elim: ∀ b1,b2:bool. ∀ P:bool → Prop.
match b1 with
 [ true ⇒ P true
 | false ⇒ P b2] → P (orb b1 b2).
#b1; #b2; #P; nelim b1; nnormalize; //; nqed.

ndefinition if_then_else: ∀A:Type. bool → A → A → A ≝ 
λA:Type.λb:bool.λ P,Q:A. match b with
 [ true ⇒ P
 | false  ⇒ Q].

(*
ntheorem fff: false ≠ true.
/2/;
//; nqed. *)

ntheorem bool_to_decidable_eq:
 ∀b1,b2:bool. decidable (b1=b2).
#b1; #b2; ncases b1; ncases b2; /2/;
@2;/3/; nqed.

ntheorem true_or_false:
∀b:bool. b = true ∨ b = false.
#b; ncases b; /2/; nqed.


(*
theorem P_x_to_P_x_to_eq:
 \forall A:Set. \forall P: A \to bool.
  \forall x:A. \forall p1,p2:P x = true. p1 = p2.
 intros.
 apply eq_to_eq_to_eq_p_q.
 exact bool_to_decidable_eq.
qed.


(* some basic properties of and - or*)
theorem andb_sym: \forall A,B:bool.
(A \land B) = (B \land A).
intros.
elim A;
  elim B;
    simplify;
    reflexivity.
qed.

theorem andb_assoc: \forall A,B,C:bool.
(A \land (B \land C)) = ((A \land B) \land C).
intros.
elim A;
  elim B;
    elim C;
      simplify;
      reflexivity.
qed.

theorem orb_sym: \forall A,B:bool.
(A \lor B) = (B \lor A).
intros.
elim A;
  elim B;
    simplify;
    reflexivity.
qed.

theorem true_to_true_to_andb_true: \forall A,B:bool.
A = true \to B = true \to (A \land B) = true.
intros.
rewrite > H.
rewrite > H1.
reflexivity.
qed. *)
