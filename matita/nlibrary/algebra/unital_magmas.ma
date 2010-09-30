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

include "algebra/magmas.ma".

nrecord unital_magma_type : Type[1] ≝
 { umt_magma:> magma_type;
   unit: umt_magma;
   umt_is_neutral_l: ∀x. op ? unit x = x;
   umt_is_neutral_r: ∀x. op ? x unit = x
 }.

nrecord unital_magma (A: unital_magma_type) : Type[1] ≝
 { um_magma:> magma A;
   neutral_closed: unit A ∈ um_magma
 }.