
(* XXX coercions *)
axiom A: Type.
axiom B: Type.
axiom cAB: A -> B.
coercion cic:/matita/tests/push_pop_status/cAB.con.

inductive eq (A:Type) (x:A) : A \to Prop \def
    refl_eq : eq A x x.

(* XXX notation *)
notation "hvbox(a break === b)" non associative with precedence 45 for @{ 'eqqq $a $b }.
interpretation "test" 'eqqq x y = (cic:/matita/tests/push_pop_status/eq.ind#xpointer(1/1) _ x y).

theorem eq_rect':
 \forall A. \forall x:A. \forall P: \forall y:A. x===y \to Type.
  P ? (refl_eq ? x) \to \forall y:A. \forall p:x===y. P y p.
 intros.
 exact
  (match p1 return \lambda y. \lambda p.P y p with
    [refl_eq \Rightarrow p]).
qed.
 
lemma sym_eq : \forall A:Type.\forall x,y:A. x===y  \to y===x.
intros.elim H. apply refl_eq.
qed.

lemma trans_eq : \forall A:Type.\forall x,y,z:A. x===y  \to y===z \to x===z.
intros.elim H1.assumption.
qed.

theorem eq_elim_r:
 \forall A:Type.\forall x:A. \forall P: A \to Prop.
   P x \to \forall y:A. y===x \to P y.
intros. elim (sym_eq ? ? ? H1).assumption.
qed.

theorem eq_elim_r':
 \forall A:Type.\forall x:A. \forall P: A \to Set.
   P x \to \forall y:A. y===x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem eq_elim_r'':
 \forall A:Type.\forall x:A. \forall P: A \to Type.
   P x \to \forall y:A. y===x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem eq_f: \forall  A,B:Type.\forall f:A\to B.
\forall x,y:A. x===y \to f x === f y.
intros.elim H.apply refl_eq.
qed.

theorem eq_f': \forall  A,B:Type.\forall f:A\to B.
\forall x,y:A. x===y \to f y === f x.
intros.elim H.apply refl_eq.
qed.

(* XXX defaults *)
default "equality"
 cic:/matita/tests/push_pop_status/eq.ind
 cic:/matita/tests/push_pop_status/sym_eq.con
 cic:/matita/tests/push_pop_status/trans_eq.con
 cic:/matita/tests/push_pop_status/eq_ind.con
 cic:/matita/tests/push_pop_status/eq_elim_r.con
 cic:/matita/tests/push_pop_status/eq_rec.con
 cic:/matita/tests/push_pop_status/eq_elim_r'.con
 cic:/matita/tests/push_pop_status/eq_rect.con
 cic:/matita/tests/push_pop_status/eq_elim_r''.con
 cic:/matita/tests/push_pop_status/eq_f.con
 cic:/matita/tests/push_pop_status/eq_f'.con. (* \x.sym (eq_f x) *)
 
include "push_pop_status_aux1.ma".
(* include "push_pop_status_aux2.ma". *)

(* XXX default *)
theorem prova: \forall x:A. eq A x x.
intros. reflexivity.
qed.

(* XXX notation *)
theorem prova1: \forall x:A. x === x.
intros. apply refl_eq.
qed.

(* XXX coercion *)
theorem pippo: A -> B.
intro a.
apply (a : B).
qed.

definition X := b.


