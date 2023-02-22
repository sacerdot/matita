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

include "logic/equality.ma".
include "higher_order_defs/functions.ma".

inductive bool : Set \def 
  | true : bool
  | false : bool.

theorem bool_elim: \forall P:bool \to Prop. \forall b:bool.
  (b = true \to P true)
  \to (b = false \to P false)
  \to P b.
  intros 2 (P b).
  elim b;
  [ apply H; reflexivity
  | apply H1; reflexivity
  ]
qed.

theorem not_eq_true_false : true \neq false.
unfold Not.intro.
change with 
match true with
[ true \Rightarrow False
| false \Rightarrow True].
rewrite > H.simplify.exact I.
qed.

definition notb : bool \to bool \def
\lambda b:bool. 
 match b with 
 [ true \Rightarrow false
 | false \Rightarrow true ].

(* FG: interpretation right after definition *)
interpretation "boolean not" 'not x = (notb x).

theorem notb_elim: \forall b:bool.\forall P:bool \to Prop.
match b with
[ true \Rightarrow P false
| false \Rightarrow P true] \to P (notb b).
intros 2.elim b.exact H. exact H.
qed.

theorem notb_notb: \forall b:bool. notb (notb b) = b.
intros.
elim b;reflexivity.
qed.

theorem injective_notb: injective bool bool notb.
unfold injective.
intros.
rewrite < notb_notb.
rewrite < (notb_notb y).
apply eq_f.
assumption.
qed.

definition andb : bool \to bool \to bool\def
\lambda b1,b2:bool. 
 match b1 with 
 [ true \Rightarrow b2
 | false \Rightarrow false ].

interpretation "boolean and" 'and x y = (andb x y).

theorem andb_elim: \forall b1,b2:bool. \forall P:bool \to Prop.
match b1 with
[ true \Rightarrow P b2
| false \Rightarrow P false] \to P (b1 \land b2).
intros 3.elim b1.exact H. exact H.
qed.

theorem and_true: \forall a,b:bool. 
andb a b =true \to a =true \land b= true.
intro.elim a
  [split
    [reflexivity|assumption]
  |apply False_ind.
   apply not_eq_true_false.
   apply sym_eq.
   assumption
  ]
qed.

theorem andb_true_true: \forall b1,b2. (b1 \land b2) = true \to b1 = true.
intro. elim b1.
reflexivity.
assumption.
qed.

theorem andb_true_true_r: \forall b1,b2. (b1 \land b2) = true \to b2 = true.
intro. elim b1
  [assumption
  |apply False_ind.apply not_eq_true_false.
   apply sym_eq.assumption
  ]
qed.

definition orb : bool \to bool \to bool\def
\lambda b1,b2:bool. 
 match b1 with 
 [ true \Rightarrow true
 | false \Rightarrow b2].

(* FG: interpretation right after definition *)
interpretation "boolean or" 'or x y = (orb x y).

theorem orb_elim: \forall b1,b2:bool. \forall P:bool \to Prop.
match b1 with
[ true \Rightarrow P true
| false \Rightarrow P b2] \to P (orb b1 b2).
intros 3.elim b1.exact H. exact H.
qed.

definition if_then_else : bool \to Prop \to Prop \to Prop \def 
\lambda b:bool.\lambda P,Q:Prop.
match b with
[ true \Rightarrow P
| false  \Rightarrow Q].

(*CSC: missing notation for if_then_else *)

theorem bool_to_decidable_eq:
 \forall b1,b2:bool. decidable (b1=b2).
 intros.
 unfold decidable.
 elim b1.
  elim b2.
   left. reflexivity.
   right. exact not_eq_true_false.
  elim b2.
   right. unfold Not. intro.
   apply not_eq_true_false.
   symmetry. exact H.
   left. reflexivity.
qed.

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
qed.
