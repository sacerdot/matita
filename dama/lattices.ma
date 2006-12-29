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

record is_lattice (C:Type) (join,meet:C→C→C) : Prop \def
 { (* abelian semigroup properties *)
   l_comm_j: symmetric ? join;
   l_associative_j: associative ? join;
   l_comm_m: symmetric ? meet;
   l_associative_m: associative ? meet;
   (* other properties *)
   l_adsorb_j_m: ∀f,g:C. join f (meet f g) = f;
   l_adsorb_m_j: ∀f,g:C. meet f (join f g) = f
 }.

record lattice : Type \def
 { l_carrier:> Type;
   l_join: l_carrier→l_carrier→l_carrier;
   l_meet: l_carrier→l_carrier→l_carrier;
   l_lattice_properties:> is_lattice ? l_join l_meet
 }.

interpretation "Lattice meet" 'and a b =
 (cic:/matita/lattices/l_meet.con _ a b).

interpretation "Lattice join" 'or a b =
 (cic:/matita/lattices/l_join.con _ a b).

definition le \def λL:lattice.λf,g:L. (f ∧ g) = f.

definition ordered_set_of_lattice: lattice → ordered_set.
 intros (L);
 apply mk_ordered_set;
  [2: apply (le L)
  | skip
  | apply mk_is_order_relation;
     [ unfold reflexive;
       intros;
       unfold;
       rewrite < (l_adsorb_j_m ? ? ? L ? x) in ⊢ (? ? (? ? ? %) ?);
       rewrite > l_adsorb_m_j;
        [ reflexivity
        | apply (l_lattice_properties L)
        ]
     | intros;
       unfold transitive;
       unfold le;
       intros;
       rewrite < H;
       rewrite > (l_associative_m ? ? ? L);
       rewrite > H1;
       reflexivity
     | unfold antisimmetric;
       unfold le;
       intros;
       rewrite < H;
       rewrite > (l_comm_m ? ? ? L);
       assumption
     ]
  ]
qed.

coercion cic:/matita/lattices/ordered_set_of_lattice.con.