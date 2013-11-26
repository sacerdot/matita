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

include "arithmetics/nat.ma".
include "ground_2/notation/constructors/infinity_0.ma".

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
