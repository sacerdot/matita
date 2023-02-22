
include "logic/equality.ma".
(* Inclusion of: LAT008-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : LAT008-1 : TPTP v3.1.1. Released v2.2.0. *)
(*  Domain   : Lattice Theory (Distributive lattices) *)
(*  Problem  : Sholander's basis for distributive lattices, part 5 (of 6). *)
(*  Version  : [MP96] (equality) axioms. *)
(*  English  : This is part of the proof that Sholanders 2-basis for *)
(*             distributive lattices is correct. Here we prove the absorption  *)
(*             law  x v (x ^ y) = x. *)
(*  Refs     : [McC98] McCune (1998), Email to G. Sutcliffe *)
(*           : [MP96]  McCune & Padmanabhan (1996), Automated Deduction in Eq *)
(*  Source   : [McC98] *)
(*  Names    : LT-3-f [MP96] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.07 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   1 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments : *)
(* -------------------------------------------------------------------------- *)
(* ----Sholander's 2-basis for distributive lattices: *)
(* ----Denial of the conclusion: *)
theorem prove_absorbtion_dual:
 \forall Univ:Set.
\forall a:Univ.
\forall b:Univ.
\forall join:\forall _:Univ.\forall _:Univ.Univ.
\forall meet:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall X:Univ.\forall Y:Univ.\forall Z:Univ.eq Univ (meet X (join Y Z)) (join (meet Z X) (meet Y X)).
\forall H1:\forall X:Univ.\forall Y:Univ.eq Univ (meet X (join X Y)) X.eq Univ (join a (meet a b)) a
.
intros.
autobatch paramodulation timeout=100;
try assumption.
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
