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

include "preamble.ma".

(* PREDICATES *********************************************************)

definition u0_predicate1: Type[0] → Type[1] ≝ λT.T → Prop.

definition u0_predicate2: Type[0] → Type[1] ≝ λT.T → u0_predicate1 T.

definition u1_predicate1: Type[1] → Type[2] ≝ λT.T → Prop.

definition u1_predicate2: Type[1] → Type[2] ≝ λT.T → u1_predicate1 T.

definition u0_full: ∀T:Type[0]. u0_predicate1 T ≝ λT,a. ⊤.

definition u0_empty: ∀T:Type[0]. u0_predicate1 T ≝ λT,a. ⊥.

definition u0_quantifier: Type[0] → Type[2] ≝ λT. u1_predicate2 (u0_predicate1 T).

definition u0_all: ∀T:Type[0]. u0_quantifier T ≝ λT,I,P. ∀a. I a → P a.

definition u0_ex: ∀T:Type[0]. u0_quantifier T ≝ λT,I,P. ∃a. I a ∧ P a.

definition u0_refl (T:Type[0]) (I:u0_predicate1 T) (P:u0_predicate2 T): Prop ≝
                   u0_all T I (λa. P a a).

definition u0_sym (T:Type[0]) (I:u0_predicate1 T) (P:u0_predicate2 T): Prop ≝
                  u0_all T I (λa1. u0_all T I (λa2. P a2 a1 → P a1 a2)).

definition u0_trans (T:Type[0]) (I:u0_predicate1 T) (P:u0_predicate2 T): Prop ≝
                    u0_all T I (λa1. u0_all T I (λa. P a1 a → (u0_all T I (λa2. P a a2 → P a1 a2)))).

definition u0_conf (T:Type[0]) (I:u0_predicate1 T) (P:u0_predicate2 T): Prop ≝
                   u0_all T I (λa. u0_all T I (λa1. P a a1 → (u0_all T I (λa2. P a a2 → P a1 a2)))).

definition u0_div (T:Type[0]) (I:u0_predicate1 T) (P:u0_predicate2 T): Prop ≝
                  u0_all T I (λa1. u0_all T I (λa. P a1 a → (u0_all T I (λa2. P a2 a → P a1 a2)))).

definition u0_repl2 (T:Type[0]) (I:u0_predicate1 T) (Q:u0_predicate2 T) (P:u0_predicate2 T): Prop ≝
                    u0_all T I (λa1. u0_all T I (λa2. P a1 a2 → u0_all T I (λb1. u0_all T I (λb2. Q b1 a1 → Q b2 a2 → P b1 b2)))).

definition u0_hom1 (T:Type[0]) (I:u0_predicate1 T) (U:Type[0]) (f:T → U) (P:u0_predicate1 T) (Q:u0_predicate1 U) : Prop ≝
                   u0_all T I (λa. P a → Q (f a)).

definition u0_hom2 (T:Type[0]) (I:u0_predicate1 T) (U:Type[0]) (f:T → U) (P:u0_predicate2 T) (Q:u0_predicate2 U) : Prop ≝
                   u0_all T I (λa1. u0_all T I (λa2. P a1 a2 → Q (f a1) (f a2))).

definition u0_xeq (T:Type[0]) (I:u0_predicate1 T) (U:Type[0]) (Q:u0_predicate2 U): u0_predicate2 (T → U) ≝
                  λf,g. u0_all T I (λa. Q (f a) (g a)).

(* Basic properties ***************************************************)

lemma u0_refl_repl_sym: ∀T,I,P. u0_refl T I P → u0_repl2 T I P P → u0_sym T I P.
normalize /3 width=7 by/ qed-.

lemma u0_refl_repl_trans: ∀T,I,P. u0_refl T I P → u0_repl2 T I P P → u0_trans T I P.
normalize /3 width=7 by/ qed-.

lemma u0_refl_repl_conf: ∀T,I,P. u0_refl T I P → u0_repl2 T I P P → u0_conf T I P.
#T #I #P
(*
/3 width=1 by (u0_refl_repl_trans T I P), (u0_refl_repl_sym T I P)/ 
*)
#H1 #H2 #a #Ha #a1 #Ha1 #Haa1
@(u0_refl_repl_trans T I P) /2 width=7 by/
@(u0_refl_repl_sym T I P) /2 width=7 by/
qed-.

lemma u0_refl_repl_div: ∀T,I,P. u0_refl T I P → u0_repl2 T I P P → u0_div T I P.
#T #I #P #H1 #H2 #a1 #Ha1 #a #Ha #Ha1a #a2 #Ha2 #Ha2a
@(u0_refl_repl_trans T I P … a) /2 width=7 by/
@(u0_refl_repl_sym T I P) /2 width=7 by/
qed-.
