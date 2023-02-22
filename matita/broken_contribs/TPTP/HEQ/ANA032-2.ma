set "baseuri" "cic:/matita/TPTP/ANA032-2".
include "logic/equality.ma".

(* Inclusion of: ANA032-2.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : ANA032-2 : TPTP v3.2.0. Released v3.2.0. *)

(*  Domain   : Analysis *)

(*  Problem  : Problem about Big-O notation *)

(*  Version  : [Pau06] axioms : Reduced > Especial. *)

(*  English  :  *)

(*  Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe *)

(*  Source   : [Pau06] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.43 v3.2.0 *)

(*  Syntax   : Number of clauses     :   11 (   0 non-Horn;   3 unit;   8 RR) *)

(*             Number of atoms       :   21 (   2 equality) *)

(*             Maximal clause size   :    4 (   2 average) *)

(*             Number of predicates  :    7 (   0 propositional; 1-3 arity) *)

(*             Number of functors    :    9 (   4 constant; 0-3 arity) *)

(*             Number of variables   :   30 (  20 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : The problems in the [Pau06] collection each have very many axioms, *)

(*             of which only a small selection are required for the refutation. *)

(*             The mission is to find those few axioms, after which a refutation *)

(*             can be quite easily found. This version has only the necessary *)

(*             axioms. *)

(* ------------------------------------------------------------------------------ *)
theorem cls_conjecture_1:
 ∀Univ:Set.∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀V_c:Univ.∀c_0:Univ.∀c_HOL_Oabs:∀_:Univ.∀_:Univ.Univ.∀c_lessequals:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_times:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀class_OrderedGroup_Oab__semigroup__mult:∀_:Univ.Prop.∀class_OrderedGroup_Olordered__ab__group__abs:∀_:Univ.Prop.∀class_OrderedGroup_Osemigroup__mult:∀_:Univ.Prop.∀class_Ring__and__Field_Opordered__semiring:∀_:Univ.Prop.∀t_b:Univ.∀v_b:∀_:Univ.Univ.∀v_c:Univ.∀v_f:∀_:Univ.Univ.∀v_g:∀_:Univ.Univ.∀v_x:Univ.∀H0:c_lessequals (c_HOL_Oabs (v_b v_x) t_b) (c_times v_c (c_HOL_Oabs (v_g v_x) t_b) t_b) t_b.∀H1:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀V_c:Univ.∀_:c_lessequals c_0 V_c T_a.∀_:c_lessequals V_a V_b T_a.∀_:class_Ring__and__Field_Opordered__semiring T_a.c_lessequals (c_times V_c V_a T_a) (c_times V_c V_b T_a) T_a.∀H2:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀_:class_OrderedGroup_Oab__semigroup__mult T_a.eq Univ (c_times V_a V_b T_a) (c_times V_b V_a T_a).∀H3:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀V_c:Univ.∀_:class_OrderedGroup_Osemigroup__mult T_a.eq Univ (c_times (c_times V_a V_b T_a) V_c T_a) (c_times V_a (c_times V_b V_c T_a) T_a).∀H4:∀T_a:Univ.∀V_a:Univ.∀_:class_OrderedGroup_Olordered__ab__group__abs T_a.c_lessequals c_0 (c_HOL_Oabs V_a T_a) T_a.c_lessequals (c_times (c_HOL_Oabs (v_b v_x) t_b) (c_HOL_Oabs (v_f v_x) t_b) t_b) (c_times v_c (c_times (c_HOL_Oabs (v_f v_x) t_b) (c_HOL_Oabs (v_g v_x) t_b) t_b) t_b) t_b
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* ------------------------------------------------------------------------------ *)
