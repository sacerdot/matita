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

include "ground/relocation/pr_pat_tls.ma".
include "ground/relocation/pr_isf_tls.ma".
include "ground/relocation/pr_ist_tls.ma".
include "ground/relocation/pr_coafter_nat_tls.ma".
include "ground/relocation/pr_coafter_isi.ma".

(* RELATIONAL CO-COMPOSITION FOR PARTIAL RELOCATION MAPS ********************)

(*** H_coafter_isfin2_fwd *)
definition H_pr_coafter_des_ist_isf: predicate pr_map â
           Îťf1. âf2. đâ¨f2âŠ â đâ¨f1âŠ â âf. f1 ~â f2 â f â  đâ¨fâŠ.

(* Destructions with pr_ist and pr_isf **************************************)

(*** coafter_isfin2_fwd_O_aux *)
fact pr_coafter_des_ist_isf_unit_aux:
     âf1. ďź â§Łâ¨đ, f1âŠ â đ â H_pr_coafter_des_ist_isf f1.
#f1 #Hf1 #f2 #H
generalize in match Hf1; generalize in match f1; -f1
@(pr_isf_ind âŚ H) -f2
[ /3 width=4 by pr_coafter_isi_inv_dx, pr_isf_isi/ ]
#f2 #_ #IH #f1 #H #Hf1 #f #Hf
elim (pr_pat_inv_unit_bi âŚ H) -H [ |*: // ] #g1 #H1
lapply (pr_ist_inv_push âŚ Hf1 âŚ H1) -Hf1 #Hg1
elim (Hg1 (đ)) #n #Hn
[ elim (pr_coafter_inv_push_bi âŚ Hf) | elim (pr_coafter_inv_push_next âŚ Hf)
] -Hf [1,6: |*: // ] #g #Hg #H0 destruct
/5 width=6 by pr_isf_next, pr_isf_push, pr_isf_inv_tls, pr_ist_tls, pr_pat_unit_succ_tls, pr_coafter_tls_sn_tls/
qed-.

(*** coafter_isfin2_fwd_aux *)
fact pr_coafter_des_ist_isf_aux:
     (âf1. ďź â§Łâ¨đ, f1âŠ â đ â H_pr_coafter_des_ist_isf f1) â
     âi2,f1. ďź â§Łâ¨đ, f1âŠ â i2 â H_pr_coafter_des_ist_isf f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #f2 #Hf2 #H2f1 #f #Hf
elim (pr_pat_inv_unit_succ âŚ H1f1) -H1f1 [ |*: // ] #g1 #Hg1 #H1
elim (pr_coafter_inv_next_sn âŚ Hf âŚ H1) -Hf #g #Hg #H0
lapply (IH âŚ Hg1 âŚ Hg) -i2 -Hg
/2 width=4 by pr_ist_inv_next, pr_isf_push/ (* * full auto fails *)
qed-.

(*** coafter_isfin2_fwd *)
lemma pr_coafter_des_ist_isf: âf1. H_pr_coafter_des_ist_isf f1.
#f1 #f2 #Hf2 #Hf1 cases (Hf1 (đ))
/3 width=7 by pr_coafter_des_ist_isf_aux, pr_coafter_des_ist_isf_unit_aux/
qed-.
