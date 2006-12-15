(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/lattices/".

include "ordered_sets.ma".

record pre_lattice (C:Type) : Type \def
 { join_: C → C → C;
   meet_: C → C → C
 }.

definition carrier_of_lattice ≝ λC:Type.λL:pre_lattice C.C.

coercion cic:/matita/lattices/carrier_of_lattice.con.

definition join : ∀C.∀L:pre_lattice C.L→L→L ≝ join_.
definition meet : ∀C.∀L:pre_lattice C.L→L→L ≝ meet_.

interpretation "Lattice meet" 'and a b =
 (cic:/matita/lattices/meet.con _ _ a b).

interpretation "Lattice join" 'or a b =
 (cic:/matita/lattices/join.con _ _ a b).

record is_lattice (C:Type) (L:pre_lattice C) : Prop \def
 { (* abelian semigroup properties *)
   l_comm_j: symmetric ? (join ? L);
   l_associative_j: associative ? (join ? L);
   l_comm_m: symmetric ? (meet ? L);
   l_associative_m: associative ? (meet ? L);
   (* other properties *)
   l_adsorb_j_m: ∀f,g:L. (f ∨ f ∧ g) = f;
   l_adsorb_m_j: ∀f,g:L. (f ∧ (f ∨ g)) = f
 }.

record lattice (C:Type) : Type \def
 { l_pre_lattice:> pre_lattice C;
   l_lattice_properties:> is_lattice ? l_pre_lattice
 }.

definition le \def λC:Type.λL:lattice C.λf,g:L. (f ∧ g) = f.

definition ordered_set_of_lattice: ∀C.lattice C → ordered_set C.
 intros;
 apply mk_ordered_set;
  [ apply mk_pre_ordered_set;
    apply (le ? l)
  | apply mk_is_order_relation;
     [ unfold reflexive;
       intros;
       unfold;
       simplify;
       unfold le;
       change in x with (carrier_of_lattice ? l);
       rewrite < (l_adsorb_j_m ? ? l ? x) in ⊢ (? ? (? ? ? ? %) ?);
       rewrite > l_adsorb_m_j;
        [ reflexivity
        | apply (l_lattice_properties ? l)
        ]
     | intros;
       unfold transitive;
       simplify;
       unfold le;
       intros;
       rewrite < H;
       rewrite > (l_associative_m ? ? l);
       rewrite > H1;
       reflexivity
     | unfold antisimmetric;
       unfold os_le;
       simplify;
       unfold le;
       intros;
       rewrite < H;
       rewrite > (l_comm_m ? ? l);
       assumption
     ]
  ]
qed.

coercion cic:/matita/lattices/ordered_set_of_lattice.con.

(*
interpretation "Lattice le" 'leq a b =
 (cic:/matita/integration_algebras/le.con _ _ a b).

definition lt \def λC:Type.λL:lattice C.λf,g. le ? L f g ∧ f ≠ g.

interpretation "Lattice lt" 'lt a b =
 (cic:/matita/integration_algebras/lt.con _ _ a b).
*)

(* The next coercion introduces a cycle in the coercion graph with
   unexpected bad results
coercion cic:/matita/integration_algebras/carrier_of_lattice.con.
*)
