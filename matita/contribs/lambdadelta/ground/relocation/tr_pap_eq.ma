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

include "ground/lib/stream_eq.ma".
include "ground/relocation/tr_pap.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(* Main constructions with stream_eq ****************************************)

(* Note: a better statement would be: tr_eq_repl … (λf1,f2. f1@❨i❩ = f2@❨i❩) *)
(*** apply_eq_repl *)
theorem apply_eq_repl (i):
        ∀f1,f2. f1 ≗ f2 → f1@❨i❩ = f2@❨i❩.
#i elim i -i [2: #i #IH ] * #p1 #f1 * #p2 #f2 #H
elim (stream_eq_inv_cons_bi … H) -H [1,8: |*: // ] #Hp #Hf //
<tr_pap_succ <tr_pap_succ /3 width=1 by eq_f2/
qed.

(* Main inversions with stream_eq *******************************************)

corec theorem nstream_eq_inv_ext:
              ∀f1,f2. (∀i. f1@❨i❩ = f2@❨i❩) → f1 ≗ f2.
* #p1 #f1 * #p2 #f2 #Hf @stream_eq_cons
[ @(Hf (𝟏))
| @nstream_eq_inv_ext -nstream_eq_inv_ext #i
  lapply (Hf (𝟏)) <tr_pap_unit <tr_pap_unit #H destruct
  lapply (Hf (↑i)) <tr_pap_succ <tr_pap_succ #H
  /3 width=2 by eq_inv_pplus_bi_dx, eq_inv_psucc_bi/
]
qed-.
