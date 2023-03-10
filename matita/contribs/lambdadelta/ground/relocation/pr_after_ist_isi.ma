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

include "ground/relocation/pr_ist_isi.ma".
include "ground/relocation/pr_after_ist.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(* Destructions with pr_ist and pr_isi **************************************)

(*** after_fwd_isid_sn *)
lemma pr_after_des_ist_eq_sn:
      âf2,f1,f. đâ¨fâŠ â f2 â f1 â f â f1 â f â đâ¨f2âŠ.
#f2 #f1 #f #H #Hf elim (pr_after_inv_ist âŚ Hf H) -H
#Hf2 #Hf1 #H @pr_isi_pat_total // -Hf2
#i2 #i #Hf2 elim (Hf1 i2) -Hf1
#i0 #Hf1 lapply (pr_pat_increasing âŚ Hf1)
#Hi20 lapply (pr_after_des_pat_sn âŚ i0 âŚ Hf1 âŚ Hf) -Hf
/3 width=7 by pr_pat_eq_repl_back, pr_pat_mono, pr_pat_id_le/
qed-.

(*** after_fwd_isid_dx *)
lemma pr_after_des_ist_eq_dx:
      âf2,f1,f.  đâ¨fâŠ â f2 â f1 â f â f2 â f â đâ¨f1âŠ.
#f2 #f1 #f #H #Hf elim (pr_after_inv_ist âŚ Hf H) -H
#Hf2 #Hf1 #H2 @pr_isi_pat_total // -Hf1
#i1 #i2 #Hi12 elim (pr_after_des_ist_pat âŚ Hi12 âŚ Hf) -f1
/3 width=8 by pr_pat_inj, pr_pat_eq_repl_back/
qed-.
