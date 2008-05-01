
include "logic/equality.ma".
(* Inclusion of: COL050-1.p *)
(* -------------------------------------------------------------------------- *)
(*  File     : COL050-1 : TPTP v3.1.1. Released v1.0.0. *)
(*  Domain   : Combinatory Logic *)
(*  Problem  : The Significance of the Mockingbird *)
(*  Version  : Especial. *)
(*  English  : There exists a mocking bird. For all birds x and y, there  *)
(*             exists a bird z that composes x with y for all birds w. Prove  *)
(*             that every bird is fond of at least one other bird. *)
(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)
(*  Source   : [ANL] *)
(*  Names    : bird1.ver1.in [ANL] *)
(*  Status   : Unsatisfiable *)
(*  Rating   : 0.00 v2.0.0 *)
(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)
(*             Number of atoms       :    3 (   3 equality) *)
(*             Maximal clause size   :    1 (   1 average) *)
(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)
(*             Number of functors    :    4 (   2 constant; 0-2 arity) *)
(*             Number of variables   :    5 (   0 singleton) *)
(*             Maximal term depth    :    3 (   2 average) *)
(*  Comments :  *)
(* -------------------------------------------------------------------------- *)
(* ---- There exists a mocking bird (Mock). *)
(* ----    TEx FAy [response(x,y) = response(y,y)]. *)
(* ----    response(Mock,y) = response(y,y). *)
(* ---- For all birds x and y, there exists a bird z that composes *)
(* ---- x with y for all birds w. *)
(* ----    FAx FAy TEz FAw [response(z,w) = response(x,response(y,w))] *)
(* ----    response(comp(x,y),w) = response(x,response(y,w)).  *)
(* ---- Hypothesis: Every bird is fond of at least one other bird. *)
(* ----    -FAx TEy [response(x,y) = y]. *)
(* ----    TEx FAy -[response(x,y) = y]. *)
(* ----    Letting A = x, *)
(* ----    -[response(A,y) = y]. *)
theorem prove_all_fond_of_another:
 \forall Univ:Set.
\forall a:Univ.
\forall compose:\forall _:Univ.\forall _:Univ.Univ.
\forall mocking_bird:Univ.
\forall response:\forall _:Univ.\forall _:Univ.Univ.
\forall H0:\forall W:Univ.\forall X:Univ.\forall Y:Univ.eq Univ (response (compose X Y) W) (response X (response Y W)).
\forall H1:\forall Y:Univ.eq Univ (response mocking_bird Y) (response Y Y).\exist Y:Univ.eq Univ (response a Y) Y
.
intros.
exists[
2:
autobatch paramodulation timeout=100;
try assumption.
|
skip]
print proofterm.
qed.
(* -------------------------------------------------------------------------- *)
