include "logic/equality.ma".

(* Inclusion of: LCL133-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL133-1 : TPTP v3.7.0. Released v1.0.0. *)

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

(*  File     : LCL001-0 : TPTP v3.7.0. Released v1.0.0. *)

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

(*             Number of atoms      :    4 (   4 equality) *)

(*             Maximal clause size  :    1 (   1 average) *)

(*             Number of predicates :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors   :    3 (   1 constant; 0-2 arity) *)

(*             Number of variables  :    8 (   0 singleton) *)

(*             Maximal term depth   :    4 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_wajsberg_lemma:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀truth:Univ.
∀x:Univ.
∀y:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (implies X Y) (implies Y X).
∀H1:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
∀H2:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
∀H3:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
∀H4:∀X:Univ.eq Univ (implies truth X) X.eq Univ x y)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#implies ##.
#not ##.
#truth ##.
#x ##.
#y ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
#H4 ##.
nauto by H0,H1,H2,H3,H4 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
