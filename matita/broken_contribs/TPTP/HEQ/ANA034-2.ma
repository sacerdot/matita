set "baseuri" "cic:/matita/TPTP/ANA034-2".
include "logic/equality.ma".

(* Inclusion of: ANA034-2.p *)

(* ------------------------------------------------------------------------------ *)

(*  File     : ANA034-2 : TPTP v3.2.0. Released v3.2.0. *)

(*  Domain   : Analysis *)

(*  Problem  : Problem about Big-O notation *)

(*  Version  : [Pau06] axioms : Reduced > Especial. *)

(*  English  :  *)

(*  Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe *)

(*  Source   : [Pau06] *)

(*  Names    :  *)

(*  Status   : Unsatisfiable *)

(*  Rating   : 0.29 v3.2.0 *)

(*  Syntax   : Number of clauses     :   15 (   0 non-Horn;   6 unit;  13 RR) *)

(*             Number of atoms       :   31 (   2 equality) *)

(*             Maximal clause size   :    6 (   2 average) *)

(*             Number of predicates  :    8 (   0 propositional; 1-3 arity) *)

(*             Number of functors    :   11 (   5 constant; 0-3 arity) *)

(*             Number of variables   :   46 (  40 singleton) *)

(*             Maximal term depth    :    5 (   2 average) *)

(*  Comments : The problems in the [Pau06] collection each have very many axioms, *)

(*             of which only a small selection are required for the refutation. *)

(*             The mission is to find those few axioms, after which a refutation *)

(*             can be quite easily found. This version has only the necessary *)

(*             axioms. *)

(* ------------------------------------------------------------------------------ *)
theorem cls_conjecture_5:
 ∀Univ:Set.∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀V_c:Univ.∀V_d:Univ.∀V_x:Univ.∀V_y:Univ.∀c_0:Univ.∀c_HOL_Oabs:∀_:Univ.∀_:Univ.Univ.∀c_less:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_lessequals:∀_:Univ.∀_:Univ.∀_:Univ.Prop.∀c_times:∀_:Univ.∀_:Univ.∀_:Univ.Univ.∀class_OrderedGroup_Olordered__ab__group__abs:∀_:Univ.Prop.∀class_Orderings_Oorder:∀_:Univ.Prop.∀class_Ring__and__Field_Oordered__idom:∀_:Univ.Prop.∀class_Ring__and__Field_Opordered__cancel__semiring:∀_:Univ.Prop.∀class_Ring__and__Field_Opordered__semiring:∀_:Univ.Prop.∀t_b:Univ.∀v_a:∀_:Univ.Univ.∀v_b:∀_:Univ.Univ.∀v_c:Univ.∀v_ca:Univ.∀v_f:∀_:Univ.Univ.∀v_g:∀_:Univ.Univ.∀v_x:Univ.∀H0:eq Univ (c_times (c_times v_c v_ca t_b) (c_HOL_Oabs (c_times (v_f v_x) (v_g v_x) t_b) t_b) t_b) (c_times (c_times v_c (c_HOL_Oabs (v_f v_x) t_b) t_b) (c_times v_ca (c_HOL_Oabs (v_g v_x) t_b) t_b) t_b).∀H1:c_lessequals (c_HOL_Oabs (v_b v_x) t_b) (c_times v_ca (c_HOL_Oabs (v_g v_x) t_b) t_b) t_b.∀H2:c_lessequals (c_HOL_Oabs (v_a v_x) t_b) (c_times v_c (c_HOL_Oabs (v_f v_x) t_b) t_b) t_b.∀H3:c_less c_0 v_c t_b.∀H4:∀T_a:Univ.∀V_a:Univ.∀_:class_OrderedGroup_Olordered__ab__group__abs T_a.c_lessequals c_0 (c_HOL_Oabs V_a T_a) T_a.∀H5:∀T_a:Univ.∀V_x:Univ.∀V_y:Univ.∀_:c_less V_x V_y T_a.∀_:class_Orderings_Oorder T_a.c_lessequals V_x V_y T_a.∀H6:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀_:c_lessequals c_0 V_a T_a.∀_:c_lessequals c_0 V_b T_a.∀_:class_Ring__and__Field_Opordered__cancel__semiring T_a.c_lessequals c_0 (c_times V_a V_b T_a) T_a.∀H7:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀V_c:Univ.∀V_d:Univ.∀_:c_lessequals c_0 V_b T_a.∀_:c_lessequals c_0 V_c T_a.∀_:c_lessequals V_a V_b T_a.∀_:c_lessequals V_c V_d T_a.∀_:class_Ring__and__Field_Opordered__semiring T_a.c_lessequals (c_times V_a V_c T_a) (c_times V_b V_d T_a) T_a.∀H8:∀T_a:Univ.∀V_a:Univ.∀V_b:Univ.∀_:class_Ring__and__Field_Oordered__idom T_a.eq Univ (c_HOL_Oabs (c_times V_a V_b T_a) T_a) (c_times (c_HOL_Oabs V_a T_a) (c_HOL_Oabs V_b T_a) T_a).c_lessequals (c_HOL_Oabs (c_times (v_a v_x) (v_b v_x) t_b) t_b) (c_times (c_times v_c v_ca t_b) (c_HOL_Oabs (c_times (v_f v_x) (v_g v_x) t_b) t_b) t_b) t_b
.
intros.
autobatch depth=5 width=5 size=20 timeout=10;
try assumption.
print proofterm.
qed.

(* ------------------------------------------------------------------------------ *)
