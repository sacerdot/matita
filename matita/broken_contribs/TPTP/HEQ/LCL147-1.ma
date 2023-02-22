set "baseuri" "cic:/matita/TPTP/LCL147-1".
include "logic/equality.ma".

(* Inclusion of: LCL147-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL147-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebra) *)

(*  Problem  : A theorem in the lattice structure of Wajsberg algebras *)

(*  Version  : [Bon91] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    : Lattice structure theorem 6 [Bon91] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.71 v3.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    9 (   0 non-Horn;   7 unit;   3 RR) *)

(*             Number of atoms       :   11 (   9 equality) *)

(*             Maximal clause size   :    2 (   1 average) *)

(*             Number of predicates  :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    8 (   4 constant; 0-2 arity) *)

(*             Number of variables   :   16 (   0 singleton) *)

(*             Maximal term depth    :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ----Include Wajsberg algebra axioms  *)

(* Inclusion of: Axioms/LCL001-0.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL001-0 : TPTP v3.2.0. Released v1.0.0. *)

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

(* ----Include Wajsberg algebra lattice structure axioms  *)

(* Inclusion of: Axioms/LCL001-1.ax *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL001-1 : TPTP v3.2.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Wajsberg Algebras) *)

(*  Axioms   : Wajsberg algebra lattice structure definitions *)

(*  Version  : [Bon91] (equality) axioms. *)

(*  English  :  *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [Bon91] Bonacina (1991), Problems in Lukasiewicz Logic *)

(*  Source   : [Bon91] *)

(*  Names    :  *)

(*  Status   :  *)

(*  Syntax   : Number of clauses    :    4 (   0 non-Horn;   2 unit;   2 RR) *)

(*             Number of literals   :    6 (   4 equality) *)

(*             Maximal clause size  :    2 (   2 average) *)

(*             Number of predicates :    2 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    5 (   1 constant; 0-2 arity) *)

(*             Number of variables  :    8 (   0 singleton) *)

(*             Maximal term depth   :    4 (   2 average) *)

(*  Comments : Requires LCL001-0.ax *)

(* -------------------------------------------------------------------------- *)

(* ----Definitions of big_V and big_hat  *)

(* ----Definition of partial order  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
theorem prove_wajsberg_theorem:
 ∀Univ:Set.∀X:Univ.∀Y:Univ.∀Z:Univ.∀big_V:∀_:Univ.∀_:Univ.Univ.∀big_hat:∀_:Univ.∀_:Univ.Univ.∀implies:∀_:Univ.∀_:Univ.Univ.∀not:∀_:Univ.Univ.∀ordered:∀_:Univ.∀_:Univ.Prop.∀truth:Univ.∀x:Univ.∀y:Univ.∀z:Univ.∀H0:∀X:Univ.∀Y:Univ.∀_:eq Univ (implies X Y) truth.ordered X Y.∀H1:∀X:Univ.∀Y:Univ.∀_:ordered X Y.eq Univ (implies X Y) truth.∀H2:∀X:Univ.∀Y:Univ.eq Univ (big_hat X Y) (not (big_V (not X) (not Y))).∀H3:∀X:Univ.∀Y:Univ.eq Univ (big_V X Y) (implies (implies X Y) Y).∀H4:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.∀H5:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).∀H6:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.∀H7:∀X:Univ.eq Univ (implies truth X) X.eq Univ (implies (big_V x y) z) (big_hat (implies x z) (implies y z))
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* -------------------------------------------------------------------------- *)
