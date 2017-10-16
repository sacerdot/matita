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

include "basic_2/syntax/lenv_ext2.ma".
include "basic_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with the extension to binders of a context-sensitive relation *)

lemma cext2_d_liftable2_sn: ∀R. d_liftable2_sn … lifts R →
                            d_liftable2_sn … liftsb (cext2 R).
#R #HR #K #I1 #I2 * -I1 -I2 #I [| #T1 #T2 #HT12 ]
#b #f #L #HLK #Z1 #H
[ lapply (liftsb_inv_unit_sn … H)
| lapply (liftsb_inv_pair_sn … H) * #U1 #HTU1
] -H #H destruct /3 width=3 by ext2_unit, ex2_intro/
elim (HR … HT12 … HLK … HTU1) -HR -b -K -T1 /3 width=3 by ext2_pair, ex2_intro/
qed-. 
