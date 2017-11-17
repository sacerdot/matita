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

include "basic_2/syntax/ext2.ma".
include "basic_2/syntax/lenv.ma".

(* EXTENSION TO BINDERS OF A CONTEXT-SENSITIVE RELATION FOR TERMS ***********)

definition cext2: (lenv → relation term) → lenv → relation bind ≝
                  λR,L. ext2 (R L).

(* Basic properties *********************************************************)

lemma cext2_sym: ∀R. (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
                 ∀L1,L2,I1,I2. cext2 R L1 I1 I2 → cext2 R L2 I2 I1.
#R #HR #L1 #L2 #I1 #I2 * /3 width=2 by ext2_pair/
qed-.

lemma cext2_co: ∀R1,R2. (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
                ∀L,I1,I2. cext2 R1 L I1 I2 → cext2 R2 L I1 I2.
#R1 #R2 #HR #L #I1 #I2 * /3 width=2 by ext2_unit, ext2_pair/
qed-.
