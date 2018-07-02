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

include "ground_2/lib/arith.ma".
include "ground_2/notation/functions/infinity_0.ma".

(* NATURAL NUMBERS WITH INFINITY ********************************************)

(* the type of natural numbers with infinity *)
inductive ynat: Type[0] ≝
| yinj: nat → ynat
| Y   : ynat
.

coercion yinj.

interpretation "ynat infinity" 'Infinity = Y.

(* Inversion lemmas *********************************************************)

lemma yinj_inj: ∀m,n. yinj m = yinj n → m = n.
#m #n #H destruct //
qed-.

(* Basic properties *********************************************************)

lemma eq_ynat_dec: ∀n1,n2:ynat. Decidable (n1 = n2).
* [ #n1 ] * [1,3: #n2 ] /2 width=1 by or_introl/
[2,3: @or_intror #H destruct ]
elim (eq_nat_dec n1 n2) /4 width=1 by yinj_inj, or_intror, or_introl/
qed-.
