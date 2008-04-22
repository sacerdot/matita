

inductive eq (A:Type) (x:A) : A \to Prop \def refl_eq : eq A x x.

theorem sym_eq : \forall A:Type.\forall x,y:A. eq A x y \to eq A y x.
intros.elim H. apply refl_eq.
qed.

theorem eq_elim_r:
 \forall A:Type.\forall x:A. \forall P: A \to Prop.
   P x \to \forall y:A. eq A y x \to P y.
intros. elim (sym_eq ? ? ? H1).assumption.
qed.

theorem eq_elim_r':
 \forall A:Type.\forall x:A. \forall P: A \to Set.
   P x \to \forall y:A. eq A y x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem eq_elim_r'':
 \forall A:Type.\forall x:A. \forall P: A \to Type.
   P x \to \forall y:A. eq A y x \to P y.
intros. elim (sym_eq ? ? ? H).assumption.
qed.

theorem trans_eq : 
    \forall A:Type.\forall x,y,z:A. eq A x y \to eq A y z \to eq A x z.
intros.elim H1.assumption.
qed.

default "equality"
 cic:/matita/tests/paramodulation/BOO075-1/eq.ind
 cic:/matita/tests/paramodulation/BOO075-1/sym_eq.con
 cic:/matita/tests/paramodulation/BOO075-1/trans_eq.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_ind.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_elim_r.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_rec.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_elim_r'.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_rect.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_elim_r''.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_f.con
 cic:/matita/tests/paramodulation/BOO075-1/eq_f1.con.

theorem eq_f: \forall  A,B:Type.\forall f:A\to B.
  \forall x,y:A. eq A x y \to eq B (f x) (f y).
intros.elim H.reflexivity.
qed.

theorem eq_f1: \forall  A,B:Type.\forall f:A\to B.
  \forall x,y:A. eq A x y \to eq B (f y) (f x).
intros.elim H.reflexivity.
qed.

inductive ex (A:Type) (P:A \to Prop) : Prop \def
    ex_intro: \forall x:A. P x \to ex A P.
interpretation "exists" 'exists \eta.x =
  (cic:/matita/tests/paramodulation/BOO075-1/ex.ind#xpointer(1/1) _ x).

notation < "hvbox(\exists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.


(* Inclusion of: BOO075-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : BOO075-1 : TPTP v3.1.1. Released v2.6.0. *)
(*  Domain   : Boolean Algebra *)
(*  Problem  : Sh-1 is a single axiom for Boolean algebra, part 1 *)
(*  Version  : [EF+02] axioms. *)
(*  English  :  *)
(*  Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in *)
(*           : [MV+02] McCune et al. (2002), Short Single Axioms for Boolean *)
(*  Source   : [TPTP] *)
(*  Names    :  *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.6.0 *)
(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)
(*             Number of atoms       :    2 (   2 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    3 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    3 (   1 singleton) *)
(*             Maximal term depth    :    5 (   2 average) *)
(*  Comments : A UEQ part of BOO039-1 *)
(* -------------------------------------------------------------------------- *)
theorem prove_meredith_2_basis_1:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall nand:Univ\rarr Univ\rarr Univ.
\forall H0:\forall A:Univ.\forall B:Univ.\forall C:Univ.eq Univ (nand (nand A (nand (nand B A) A)) (nand B (nand C A))) B.eq Univ (nand (nand a a) (nand b a)) a
.
intros.
autobatch paramodulation timeout=600;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
