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

include "nat/big_ops.ma".
include "algebra/unital_magmas.ma".
include "algebra/abelian_magmas.ma".

nlet rec plus (n:nat) (m:nat) on n : nat ≝
 match n with
  [ O ⇒ m
  | S n' ⇒ S (plus n' m) ].

interpretation "natural plus" 'plus x y = (plus x y).

ndefinition plus_magma_type: magma_type.
 napply mk_magma_type
  [ napply NAT
  | napply mk_binary_morphism
     [ napply plus
     | #a; #a'; #b; #b'; #Ha; #Hb; nrewrite < Ha; nrewrite < Hb; napply refl ]##]
nqed.

ndefinition plus_abelian_magma_type: abelian_magma_type.
 napply mk_abelian_magma_type
  [ napply plus_magma_type
  | nnormalize; #x;
     (* nelim non va *) napply (nat_rect_CProp0 ??? x);
     ##[ #y; napply (nat_rect_CProp0 ??? y) [ napply refl | #n; #H; nnormalize; nrewrite < H; napply refl]
     ##| #n; #H; #y; nnormalize;
         (* rewrite qui non va *)
         napply (eq_rect_CProp0_r ????? (H y));
         napply (nat_rect_CProp0 ??? y)
          [ napply refl
          | #n0; #K; nnormalize in K; nnormalize;
            napply (eq_rect_CProp0 ????? K); napply refl] ##]
nqed.

ndefinition plus_unital_magma_type: unital_magma_type.
 napply mk_unital_magma_type
  [ napply plus_magma_type
  | napply O
  | #x; napply refl
  | #x; (* qua manca ancora l'hint *) napply (symm plus_abelian_magma_type) ]
nqed.

ndefinition big_plus ≝ λn.λf.big_op plus_magma_type n f O.
