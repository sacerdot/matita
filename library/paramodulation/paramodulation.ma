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

set "baseuri" "cic:/matita/paramodulation/".

include "nat/nat.ma".

definition make_eqs_smart \def 
  \lambda Univ:Type.
  \lambda length:nat.
  \lambda initial:Univ.
  let rec aux (p:Univ) (n:nat) on n : Prop \def
    match n with
    [ O \Rightarrow \forall a:Univ. p = a \to initial = a   
    | (S n) \Rightarrow \forall a:Univ. p = a \to aux a n
    ]
  in 
    aux initial length.
  
theorem transl_smart : 
  \forall Univ:Type.\forall n:nat.\forall initial:Univ.
    make_eqs_smart Univ n initial.
  intros.
  unfold make_eqs_smart.
  elim n
  [ simplify.intros.assumption
  | simplify.intros.rewrite < H1.assumption
  ]
qed.  

theorem prova:
  \forall Univ:Type.
  \forall a,b:Univ.
  \forall plus: Univ \to Univ \to Univ.
  \forall H:\forall x,y:Univ.plus x y = plus y x.
  \forall H1:plus b a = plus b b.
  plus a b = plus b b.
  intros.
  apply (transl_smart ? (S O) ? ? (H a b) ? H1).
qed. 
  
