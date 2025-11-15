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

(**) (* reverse include *)
include "ground/subsets/subset_ext_eq.ma".
include "ground/subsets/subset_listed_1.ma".
include "delayed_updating/unwind/unwind2_path_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with subset_le *********************************************)

lemma unwind2_term_le_repl_dx (f):
      compatible_2_fwd … (subset_le …) (subset_le …) (λt.▼[f]t).
/2 width=3 by subset_le_ext_f1_bi/
qed.

(* Constructions with subset_eq *********************************************)

lemma unwind2_term_eq_repl_sx (t):
      compatible_2_fwd … fbr_eq (subset_eq …) (λf.▼[f]t).
/3 width=1 by subset_eq_ext_f1_exteq, unwind2_path_eq_repl/
qed.

lemma unwind2_term_eq_repl_dx (f):
      compatible_2_fwd … (subset_eq …) (subset_eq …) (λt.▼[f]t).
/2 width=1 by subset_eq_ext_f1_bi/
qed.

(* Note: generalize with subset_ext_f1 *)
lemma unwind2_term_single (f) (p):
      ❴▼[f]p❵ ⇔ ▼[f]❴p❵.
#f #p @conj #x #H0
[ >(subset_in_inv_single ??? H0) -x
  /2 width=1 by in_comp_unwind2_bi/
| cases H0 -H0 #y #H0
  >(subset_in_inv_single ??? H0) -y
  * -x //
]
qed.
