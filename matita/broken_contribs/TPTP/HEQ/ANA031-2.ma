set "baseuri" "cic:/matita/TPTP/ANA031-2".
include "logic/equality.ma".

(* Inclusion of: ANA031-2.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : ANA031-2 : TPTP v3.2.0. Released v3.2.0. *)

(*  Domain   : Analysis *)

(*  Problem  : Problem about Big-O notation *)

(*  Version  : [Pau06] axioms : Reduced > Especial. *)

(*  English  :  *)

(*  Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe *)

(*  Source   : [Pau06] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;   3 unit;   7 RR) *)

(*             Number of atoms       :   21 (   2 equality) *)

(*             Maximal clause size   :    4 (   2 average) *)

(*             Number of predicates  :    7 (   0 propositional; 1-3 arity) *)

(*             Number of functors    :    9 (   3 constant; 0-3 arity) *)

(*             Number of variables   :   32 (  20 singleton) *)

(*             Maximal term depth    :    6 (   2 average) *)

(*  Comments : The problems in the [Pau06] collection each have very many axioms, *)

(*             of which only a small selection are required for the refutation. *)

(*             The mission is to find those few axioms, after which a refutation *)

(*             can be quite easily found. This version has only the necessary *)

(*             axioms. *)

(* ------------------------------------------------------------------------------ *)
theorem cls_conjecture_1:
 ∀Univ:Set.∀V_U:Univ.∀c_HOL_Oabs:∀_:Univ.∀_:Univ.Univ.∀c_lessequals:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_times:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀t_b:Univ.∀v_b:∀_:Univ.Univ.∀v_c:Univ.∀v_f:∀_:Univ.Univ.∀v_g:∀_:Univ.Univ.∀v_x:∀_:Univ.Univ.∀H0:∀V_U:Univ.c_lessequals (c_HOL_Oabs (v_b V_U) t_b) (c_times v_c (c_HOL_Oabs (v_g V_U) t_b) t_b) t_b.∃V_U:Univ.c_lessequals (c_times (c_HOL_Oabs (v_b (v_x V_U)) t_b) (c_HOL_Oabs (v_f (v_x V_U)) t_b) t_b) (c_times V_U (c_times (c_HOL_Oabs (v_f (v_x V_U)) t_b) (c_HOL_Oabs (v_g (v_x V_U)) t_b) t_b) t_b) t_b
.
intros.
exists[
2:
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
|
skip]
print proofterm.
qed.

(* ------------------------------------------------------------------------------ *)
