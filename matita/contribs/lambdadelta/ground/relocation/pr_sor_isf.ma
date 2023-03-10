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

include "ground/relocation/pr_isf_eq.ma".
include "ground/relocation/pr_sor_fcla.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_isf ************************************************)

(*** sor_isfin_ex *)
lemma pr_sor_isf_bi:
      âf1,f2. đâ¨f1âŠ â đâ¨f2âŠ â ââf. f1 â f2 â f & đâ¨fâŠ.
#f1 #f2 * #n1 #H1 * #n2 #H2 elim (pr_sor_fcla_bi âŚ H1 âŚ H2) -H1 -H2
/3 width=4 by ex2_intro, ex_intro/
qed-.

(* Destructions with pr_isf *************************************************)

(*** sor_fwd_isfin_sn *)
lemma pr_sor_des_isf_sn:
      âf. đâ¨fâŠ â âf1,f2. f1 â f2 â f â đâ¨f1âŠ.
#f * #n #Hf #f1 #f2 #H
elim (pr_sor_des_fcla_sn âŚ Hf âŚ H) -f -f2 /2 width=2 by ex_intro/
qed-.

(*** sor_fwd_isfin_dx *)
lemma pr_sor_des_isf_dx:
      âf. đâ¨fâŠ â âf1,f2. f1 â f2 â f â đâ¨f2âŠ.
#f * #n #Hf #f1 #f2 #H
elim (pr_sor_des_fcla_dx âŚ Hf âŚ H) -f -f1 /2 width=2 by ex_intro/
qed-.

(* Inversions with pr_isf ***************************************************)

(*** sor_isfin *)
lemma pr_sor_inv_isf_bi:
      âf1,f2. đâ¨f1âŠ â đâ¨f2âŠ â âf. f1 â f2 â f â đâ¨fâŠ.
#f1 #f2 #Hf1 #Hf2 #f #Hf elim (pr_sor_isf_bi âŚ Hf1 âŚ Hf2) -Hf1 -Hf2
/3 width=6 by pr_sor_mono, pr_isf_eq_repl_back/
qed-.

(*** sor_inv_isfin3 *)
lemma pr_sor_inv_isf:
      âf1,f2,f. f1 â f2 â f â đâ¨fâŠ â
      â§â§ đâ¨f1âŠ & đâ¨f2âŠ.
/3 width=4 by pr_sor_des_isf_dx, pr_sor_des_isf_sn, conj/ qed-.
