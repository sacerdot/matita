include "logic/equality.ma".

(* Inclusion of: GRP014-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : GRP014-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Group Theory *)

(*  Problem  : Product is associative in this group theory *)

(*  Version  : [Ove90] (equality) axioms : Incomplete. *)

(*  English  : The group theory specified by the axiom given implies the  *)

(*             associativity of multiply. *)

(*  Refs     : [Ove90] Overbeek (1990), ATP competition announced at CADE-10 *)

(*           : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal  *)

(*           : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11  *)

(*           : [Zha93] Zhang (1993), Automated Proofs of Equality Problems in *)

(*  Source   : [Ove90] *)

(*  Names    : CADE-11 Competition Eq-4 [Ove90] *)

(*           : THEOREM EQ-4 [LM93] *)

(*           : PROBLEM 4 [Zha93] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.22 v3.4.0, 0.25 v3.3.0, 0.07 v3.2.0, 0.14 v3.1.0, 0.11 v2.7.0, 0.18 v2.6.0, 0.00 v2.2.1, 0.33 v2.2.0, 0.43 v2.1.0, 0.50 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    5 (   3 constant; 0-2 arity) *)

(*             Number of variables   :    4 (   0 singleton) *)

(*             Maximal term depth    :    9 (   4 average) *)

(*  Comments : The group_axiom is in fact a single axiom for group theory *)

(*             [LM93]. *)

(* -------------------------------------------------------------------------- *)
ntheorem prove_associativity:
 (∀Univ:Type.∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.
∀a:Univ.
∀b:Univ.
∀c:Univ.
∀inverse:∀_:Univ.Univ.
∀multiply:∀_:Univ.∀_:Univ.Univ.
∀H0:∀W:Univ.∀X:Univ.∀Y:Univ.∀Z:Univ.eq Univ (multiply X (inverse (multiply (multiply (inverse (multiply (inverse Y) (multiply (inverse X) W))) Z) (inverse (multiply Y Z))))) W.eq Univ (multiply a (multiply b c)) (multiply (multiply a b) c))
.
#Univ ##.
#W ##.
#X ##.
#Y ##.
#Z ##.
#a ##.
#b ##.
#c ##.
#inverse ##.
#multiply ##.
#H0 ##.
nauto by H0 ##;
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
