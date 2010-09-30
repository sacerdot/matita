include "logic/equality.ma".

(* Inclusion of: COL051-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL051-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : Egocentric mocking bird? *)

(*  Version  : Especial. *)

(*  English  : There exists a mocking bird. For all birds x and y, there  *)

(*             exists a bird z that composes x with y for all birds w. Prove  *)

(*             that there exists a bird x that is fond of itself. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*  Source   : [ANL] *)

(*  Names    : bird2.ver1.in [ANL] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    3 (   0 non-Horn;   3 unit;   1 RR) *)

(*             Number of atoms       :    3 (   3 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    3 (   1 constant; 0-2 arity) *)

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

(* ---- Hypothesis: There exists a bird x that is fond of itself. *)

(* ----    -TEx [response(x,x) = x]. *)

(* ----    FAx -[response(x,x) = x]. *)
ntheorem prove_the_bird_exists:
 (∀Univ:Type.∀W:Univ.∀X:Univ.∀Y:Univ.
∀compose:∀_:Univ.∀_:Univ.Univ.
∀mocking_bird:Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:∀W:Univ.∀X:Univ.∀Y:Univ.eq Univ (response (compose X Y) W) (response X (response Y W)).
∀H1:∀Y:Univ.eq Univ (response mocking_bird Y) (response Y Y).∃X:Univ.eq Univ (response X X) X)
.
#Univ ##.
#W ##.
#X ##.
#Y ##.
#compose ##.
#mocking_bird ##.
#response ##.
#H0 ##.
#H1 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0,H1 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
