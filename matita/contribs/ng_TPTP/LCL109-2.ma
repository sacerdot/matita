include "logic/equality.ma".

(* Inclusion of: LCL109-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL109-2 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Many valued sentential) *)

(*  Problem  : MV-4 depends on the Merideth system *)

(*  Version  : [Ove90] axioms. *)

(*             Theorem formulation : Wajsberg algebra formulation. *)

(*  English  : An axiomatisation of the many valued sentential calculus  *)

(*             is {MV-1,MV-2,MV-3,MV-5} by Meredith. Wajsberg provided  *)

(*             a different axiomatisation. Show that MV-4 depends on the  *)

(*             Wajsberg system. *)

(*  Refs     : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)

(*           : [LM92]  Lusk & McCune (1992), Experiments with ROO, a Parallel *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)

(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)

(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)

(*  Source   : [Ove90] *)

(*  Names    : CADE-11 Competition Eq-5 [Ove90] *)

(*           : Luka-5 [LM92] *)

(*           : MV4 [LW92] *)

(*           : THEOREM EQ-5 [LM93] *)

(*           : PROBLEM 5 [Zha93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.29 v3.1.0, 0.22 v2.7.0, 0.27 v2.6.0, 0.17 v2.5.0, 0.00 v2.4.0, 0.33 v2.2.1, 0.56 v2.2.0, 0.71 v2.1.0, 1.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    8 (   0 singleton) *)

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
ntheorem prove_wajsberg_mv_4:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀truth:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
∀H3:∀X:Univ.eq Univ (implies truth X) X.eq Univ (implies (implies (implies a b) (implies b a)) (implies b a)) truth)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#implies ##.
#not ##.
#truth ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
