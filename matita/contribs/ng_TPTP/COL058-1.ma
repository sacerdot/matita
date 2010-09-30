include "logic/equality.ma".

(* Inclusion of: COL058-1.p *)

(* -------------------------------------------------------------------------- *)

(*  File     : COL058-1 : TPTP v3.7.0. Released v1.0.0. *)

(*  Domain   : Combinatory Logic *)

(*  Problem  : If there's a lark, then there's an egocentric bird. *)

(*  Version  : Especial. *)

(*  English  : Suppose we are given a forest that conrtains a lark, and  *)

(*             we are not given any other information. Prove that at least  *)

(*             one bird in the forest must be egocentric. *)

(*  Refs     : [Smu85] Smullyan (1978), To Mock a Mocking Bird and Other Logi *)

(*           : [GO86]  Glickfield & Overbeek (1986), A Foray into Combinatory *)

(*  Source   : [GO86] *)

(*  Names    : - [GO86] *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.00 v2.0.0 *)

(*  Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   1 RR) *)

(*             Number of atoms       :    2 (   2 equality) *)

(*             Maximal clause size   :    1 (   1 average) *)

(*             Number of predicates  :    1 (   0 propositional; 2-2 arity) *)

(*             Number of functors    :    2 (   1 constant; 0-2 arity) *)

(*             Number of variables   :    3 (   0 singleton) *)

(*             Maximal term depth    :    3 (   2 average) *)

(*  Comments :  *)

(* -------------------------------------------------------------------------- *)

(* ---- There exists a lark  *)

(* ---- Hypothesis: There exists a bird x that is fond of itself.  *)
ntheorem prove_the_bird_exists:
 (∀Univ:Type.∀X:Univ.∀X1:Univ.∀X2:Univ.
∀lark:Univ.
∀response:∀_:Univ.∀_:Univ.Univ.
∀H0:∀X1:Univ.∀X2:Univ.eq Univ (response (response lark X1) X2) (response X1 (response X2 X2)).∃X:Univ.eq Univ (response X X) X)
.
#Univ ##.
#X ##.
#X1 ##.
#X2 ##.
#lark ##.
#response ##.
#H0 ##.
napply (ex_intro ? ? ? ?) ##[
##2:
nauto by H0 ##;
##| ##skip ##]
ntry (nassumption) ##;
nqed.

(* -------------------------------------------------------------------------- *)
