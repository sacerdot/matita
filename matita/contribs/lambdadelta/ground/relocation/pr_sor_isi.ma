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

include "ground/relocation/pr_isi_eq.ma".
include "ground/relocation/pr_sor_eq.ma".
include "ground/relocation/pr_sor_sor.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_isi ************************************************)

(*** sor_isid_sn *)
corec lemma pr_sor_isi_sn:
            âf1. đâ¨f1âŠ â âf2. f1 â f2 â f2.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pr_map_split_tl f2)
/3 width=7 by pr_sor_push_bi, pr_sor_push_next/
qed.

(*** sor_isid_dx *)
corec lemma pr_sor_isi_dx:
            âf2. đâ¨f2âŠ â âf1. f1 â f2 â f1.
#f2 * -f2
#f2 #g2 #Hf2 #H2 #f1 cases (pr_map_split_tl f1)
/3 width=7 by pr_sor_push_bi, pr_sor_next_push/
qed.

(*** sor_isid *)
lemma pr_sor_isi_bi_isi:
      âf1,f2,f. đâ¨f1âŠ â đâ¨f2âŠ â đâ¨fâŠ â f1 â f2 â f.
/4 width=3 by pr_sor_eq_repl_back_dx, pr_sor_eq_repl_back_sn, pr_isi_inv_eq_repl/ qed.


(* Destructions with pr_isi *************************************************)

(*** sor_fwd_isid1 *)
corec lemma pr_sor_des_isi_sn:
            âf1,f2,f. f1 â f2 â f â đâ¨fâŠ â đâ¨f1âŠ.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by pr_isi_inv_push, pr_isi_push/ ]
cases (pr_isi_inv_next âŚ Hg âŚ H)
qed-.

(*** sor_fwd_isid2 *)
corec lemma pr_sor_des_isi_dx:
            âf1,f2,f. f1 â f2 â f â đâ¨fâŠ â đâ¨f2âŠ.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf #H1 #H2 #H #Hg
[ /4 width=6 by pr_isi_inv_push, pr_isi_push/ ]
cases (pr_isi_inv_next âŚ Hg âŚ H)
qed-.

(* Inversions with pr_isi ***************************************************)

(*** sor_isid_inv_sn *)
lemma pr_sor_inv_isi_sn:
      âf1,f2,f. f1 â f2 â f â đâ¨f1âŠ â f2 â f.
/3 width=4 by pr_sor_isi_sn, pr_sor_mono/
qed-.

(*** sor_isid_inv_dx *)
lemma pr_sor_inv_isi_dx:
      âf1,f2,f. f1 â f2 â f â đâ¨f2âŠ â f1 â f.
/3 width=4 by pr_sor_isi_dx, pr_sor_mono/
qed-.

(*** sor_inv_isid3 *)
lemma pr_sor_inv_isi:
      âf1,f2,f. f1 â f2 â f â đâ¨fâŠ â
      â§â§ đâ¨f1âŠ & đâ¨f2âŠ.
/3 width=4 by pr_sor_des_isi_dx, pr_sor_des_isi_sn, conj/ qed-.
