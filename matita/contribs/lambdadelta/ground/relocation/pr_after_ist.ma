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

include "ground/relocation/pr_pat_lt.ma".
include "ground/relocation/pr_nat.ma".
include "ground/relocation/pr_ist.ma".
include "ground/relocation/pr_after_pat.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Destructions with pr_ist *************************************************)

(*** after_istot_fwd *)
lemma pr_after_ist_des:
      âf2,f1,f. f2 â f1 â f â đâ¨f2âŠ â đâ¨f1âŠ â đâ¨fâŠ.
#f2 #f1 #f #Hf #Hf2 #Hf1 #i1 elim (Hf1 i1) -Hf1
#i2 #Hf1 elim (Hf2 i2) -Hf2
/3 width=7 by pr_after_des_pat, ex_intro/
qed-.

(*** after_fwd_istot_dx *)
lemma pr_after_des_ist_dx:
      âf2,f1,f. f2 â f1 â f â đâ¨fâŠ â đâ¨f1âŠ.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i2 #Hf elim (pr_after_pat_des âŚ Hf âŚ H) -f /2 width=2 by ex_intro/
qed-.

(*** after_fwd_istot_sn *)
lemma pr_after_des_ist_sn:
      âf2,f1,f. f2 â f1 â f â đâ¨fâŠ â đâ¨f2âŠ.
#f2 #f1 #f #H #Hf #i1 elim (Hf i1) -Hf
#i #Hf elim (pr_after_pat_des âŚ Hf âŚ H) -f
#i2 #Hf1 #Hf2 lapply (pr_pat_increasing âŚ Hf1) -f1
#Hi12 elim (pr_pat_le_ex âŚ Hf2 âŚ Hi12) -i2 /2 width=2 by ex_intro/
qed-.

(*** after_at1_fwd *)
lemma pr_after_des_ist_pat:
      âf1,i1,i2. ďź â§Łâ¨i1, f1âŠ â i2 â âf2. đâ¨f2âŠ â âf. f2 â f1 â f â
      ââi. ďź â§Łâ¨i2, f2âŠ â i & ďź â§Łâ¨i1, fâŠ â i.
#f1 #i1 #i2 #Hf1 #f2 #Hf2 #f #Hf elim (Hf2 i2) -Hf2
/3 width=8 by pr_after_des_pat, ex2_intro/
qed-.

lemma pr_after_des_ist_nat:
      âf1,l1,l2. ďź Â§â¨l1, f1âŠ â l2 â âf2. đâ¨f2âŠ â âf. f2 â f1 â f â
      ââl. ďź Â§â¨l2, f2âŠ â l & ďź Â§â¨l1, fâŠ â l.
#f1 #l1 #l2 #H1 #f2 #H2 #f #Hf
elim (pr_after_des_ist_pat âŚ H1 âŚ H2 âŚ Hf) -f1 -H2
/2 width=3 by ex2_intro/
qed-.

(* Inversions with pr_ist ***************************************************)

(*** after_inv_istot *)
lemma pr_after_inv_ist:
      âf2,f1,f. f2 â f1 â f â đâ¨fâŠ â â§â§ đâ¨f2âŠ & đâ¨f1âŠ.
/3 width=4 by pr_after_des_ist_sn, pr_after_des_ist_dx, conj/ qed-.
