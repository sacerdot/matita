
include "logic/equality.ma".
(* Inclusion of: LCL133-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL133-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebra) *)
(*  Problem  : A lemma in Wajsberg algebras *)
(*  Version  : [Bon91] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*  Source   : [Bon91] *)
(*  Names    : Lemma 2 [Bon91] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)
(*  Syntax   : Number of clauses     :    6 (   0 non-Horn;   6 unit;   1 RR) *)
(*             Number of atoms       :    6 (   6 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)
(*             Number of variables   :   10 (   0 singleton) *)
(*             Maximal term depth    :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ----Include Wajsberg algebra axioms  *)
(* Inclusion of: Axioms/LCL001-0.ax *)
(* -------------------------------------------------------------------------- *)
(*  File     : LCL001-0 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Logic Calculi (Wajsberg Algebras) *)
(*  Axioms   : Wajsberg algebra axioms *)
(*  Version  : [Bon91] (equality) axioms. *)
(*  English  :  *)
(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)
(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)
(*           : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio *)
(*  Source   : [MW92] *)
(*  Names    : MV Sentential Calculus [MW92] *)
(*  Status   :  *)
(*  Syntax   : Number of clauses    :    4 (   0 non-Horn;   4 unit;   0 RR) *)
(*             Number of literals   :    4 (   4 equality) *)
(*             Maximal clause size  :    1 (   1 average) *)
(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors   :    3 (   1 constant; 0-2 arity) *)
(*             Number of variables  :    8 (   0 singleton) *)
(*             Maximal term depth   :    4 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
theorem prove_wajsberg_lemma:
 \forall Univ:Set.
\forall implies:\forall _:Univ.\forall _:Univ.Univ.
\forall not:\forall _:Univ.Univ.
\forall truth:Univ.
\forall x:Univ.
\forall y:Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.eq Univ (implies X Y) (implies Y X).
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
\forall H2:\forall X:Univ.\forall Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
\forall H3:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
\forall H4:\forall X:Univ.eq Univ (implies truth X) X.eq Univ x y
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
