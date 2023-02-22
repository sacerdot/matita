include "logic/equality.ma".

(* Inclusion of: LCL112-2.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : LCL112-2 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Logic Calculi (Many valued sentential) *)

(*  Problem  : MV-29 depends on the Meredith system *)

(*  Version  : [McC92] axioms. *)

(*             Theorem formulation : Wajsberg algebra formulation *)

(*  English  : An axiomatisation of the many valued sentential calculus  *)

(*             is {MV-1,MV-2,MV-3,MV-5} by Meredith. Wajsberg presented  *)

(*             an equality axiomatisation. Show that MV-29 depends on the  *)

(*             Wajsberg axiomatisation. *)

(*  Refs     : [FRT84] Font et al. (1984), Wajsberg Algebras *)

(*           : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio *)

(*           : [LW92]  Lusk & Wos (1992), Benchmark Problems in Which Equalit *)

(*           : [McC92] McCune (1992), Email to G. Sutcliffe *)

(*  Source   : [McC92] *)

(*  Names    : MV1.2 [LW92] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.2.1, 0.22 v2.2.0, 0.29 v2.1.0, 0.25 v2.0.0 *)

(*  Syntax   : Number of clauses     :    5 (   0 non-Horn;   5 unit;   1 RR) *)

(*             Number of atoms       :    5 (   5 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)

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
ntheorem prove_mv_29:
 (∀Univ:Type.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀implies:∀_:Univ.∀_:Univ.Univ.
∀not:∀_:Univ.Univ.
∀truth:Univ.
∀x:Univ.
∀H0:∀X:Univ.∀Y:Univ.eq Univ (implies (implies (not X) (not Y)) (implies Y X)) truth.
∀H1:∀X:Univ.∀Y:Univ.eq Univ (implies (implies X Y) Y) (implies (implies Y X) X).
∀H2:∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (implies (implies X Y) (implies (implies Y Z) (implies X Z))) truth.
∀H3:∀X:Univ.eq Univ (implies truth X) X.eq Univ (implies x (not (not x))) truth)
.
#Univ ##.
#X ##.
#Y ##.
#Z ##.
#implies ##.
#not ##.
#truth ##.
#x ##.
#H0 ##.
#H1 ##.
#H2 ##.
#H3 ##.
nauto by H0,H1,H2,H3 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
