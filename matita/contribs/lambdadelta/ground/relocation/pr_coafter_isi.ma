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

include "ground/relocation/pr_isi_id.ma".
include "ground/relocation/pr_coafter_coafter.ma".

(* RELATIONAL CO-COMPOSITION FOR PARTIAL RELOCATION MAPS ********************)

(* Constructions with pr_isi ************************************************)

(*** coafter_isid_sn *)
corec lemma pr_coafter_isi_sn:
            âf1. đâ¨f1âŠ â âf2. f1 ~â f2 â f2.
#f1 * -f1 #f1 #g1 #Hf1 #H1 #f2
cases (pr_map_split_tl f2) #H2
/3 width=7 by pr_coafter_push, pr_coafter_refl/
qed.

(*** coafter_isid_dx *)
corec lemma pr_coafter_isi_dx:
            âf2,f. đâ¨f2âŠ â đâ¨fâŠ â âf1. f1 ~â f2 â f.
#f2 #f * -f2 #f2 #g2 #Hf2 #H2 * -f #f #g #Hf #H #f1
cases (pr_map_split_tl f1) #H1
[ /3 width=7 by pr_coafter_refl/
| @(pr_coafter_next âŚ H1 âŚ H) /3 width=3 by pr_isi_push/
]
qed.

(* Inversions with pr_isi ***************************************************)

(*** coafter_isid_inv_sn *)
lemma pr_coafter_isi_inv_sn:
      âf1,f2,f. f1 ~â f2 â f â đâ¨f1âŠ â f2 â f.
/3 width=6 by pr_coafter_isi_sn, pr_coafter_mono/ qed-.

(*** coafter_isid_inv_dx *)
lemma pr_coafter_isi_inv_dx:
      âf1,f2,f. f1 ~â f2 â f â đâ¨f2âŠ â đâ¨fâŠ.
/4 width=4 by pr_eq_id_isi, pr_coafter_isi_dx, pr_coafter_mono/ qed-.
