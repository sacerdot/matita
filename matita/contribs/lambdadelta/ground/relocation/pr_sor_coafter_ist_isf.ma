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

include "ground/relocation/pr_isf.ma".
include "ground/relocation/pr_coafter_isi.ma".
include "ground/relocation/pr_coafter_ist_isi.ma".
include "ground/relocation/pr_sor_isi.ma".

(* RELATIONAL UNION FOR PARTIAL RELOCATION MAPS *****************************)

(* Constructions with pr_coafter and pr_ist and pr_isf **********************)

(*** coafter_sor *)
lemma pr_sor_coafter_dx_tans:
      âf. ðâ¨fâ© â âf2. ðâ¨f2â© â âf1. f2 ~â f1 â f â âf1a,f1b. f1a â f1b â f1 â
      ââfa,fb. f2 ~â f1a â fa & f2 ~â f1b â fb & fa â fb â f.
@pr_isf_ind
[ #f #Hf #f2 #Hf2 #f1 #Hf #f1a #f1b #Hf1
  lapply (pr_coafter_des_ist_sn_isi â¦ Hf ??) -Hf // #H2f1
  elim (pr_sor_inv_isi â¦ Hf1) -Hf1 //
  /3 width=5 by pr_coafter_isi_dx, pr_sor_idem, ex3_2_intro/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (pr_coafter_inv_push â¦ H1) -H1 [1,3: * |*: // ]
  [ #g2 #g1 #Hf #Hgf2 #Hgf1
    elim (pr_sor_inv_push â¦ H2) -H2 [ |*: // ] #ga #gb #Hg1
    lapply (pr_ist_inv_push â¦ Hf2 â¦ Hgf2) -Hf2 #Hg2
    elim (IH â¦ Hf â¦ Hg1) // -f1 -g1 -IH -Hg2
    /3 width=11 by pr_coafter_refl, pr_sor_push_bi, ex3_2_intro/
  | #g2 #Hf #Hgf2
    lapply (pr_ist_inv_next â¦ Hf2 â¦ Hgf2) -Hf2 #Hg2
    elim (IH â¦ Hf â¦ H2) // -f1 -IH -Hg2
    /3 width=11 by pr_coafter_next, pr_sor_push_bi, ex3_2_intro/
  ]
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (pr_coafter_inv_next â¦ H1) -H1 [ |*: // ] #g2 #g1 #Hf #Hgf2 #Hgf1
  lapply (pr_ist_inv_push â¦ Hf2 â¦ Hgf2) -Hf2 #Hg2
  elim (pr_sor_inv_next â¦ H2) -H2 [1,3,4: * |*: // ] #ga #gb #Hg1
  elim (IH â¦ Hf â¦ Hg1) // -f1 -g1 -IH -Hg2
  /3 width=11 by pr_coafter_refl, pr_coafter_push, pr_sor_next_push, pr_sor_push_next, pr_sor_next_bi, ex3_2_intro/
]
qed-.

(*** coafter_inv_sor *)
lemma pr_sor_coafter_div:
      âf. ðâ¨fâ© â âf2. ðâ¨f2â© â âf1. f2 ~â f1 â f â âfa,fb. fa â fb â f â
      ââf1a,f1b. f2 ~â f1a â fa & f2 ~â f1b â fb & f1a â f1b â f1.
@pr_isf_ind
[ #f #Hf #f2 #Hf2 #f1 #H1f #fa #fb #H2f
  elim (pr_sor_inv_isi â¦ H2f) -H2f //
  lapply (pr_coafter_des_ist_sn_isi â¦ H1f ??) -H1f //
  /3 width=5 by ex3_2_intro, pr_coafter_isi_dx, pr_sor_isi_bi_isi/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (pr_sor_inv_push â¦ H2) -H2 [ |*: // ] #ga #gb #H2f
  elim (pr_coafter_inv_push â¦ H1) -H1 [1,3: * |*: // ] #g2 [ #g1 ] #H1f #Hgf2
  [ lapply (pr_ist_inv_push â¦ Hf2 â¦ Hgf2) | lapply (pr_ist_inv_next â¦ Hf2 â¦ Hgf2) ] -Hf2 #Hg2
  elim (IH â¦ Hg2 â¦ H1f â¦ H2f) -f -Hg2
  /3 width=11 by pr_sor_push_bi, ex3_2_intro, pr_coafter_refl, pr_coafter_next/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (pr_coafter_inv_next â¦ H1) -H1 [ |*: // ] #g2 #g1 #H1f #Hgf2
  lapply (pr_ist_inv_push â¦ Hf2 â¦ Hgf2) -Hf2 #Hg2
  elim (pr_sor_inv_next â¦ H2) -H2 [1,3,4: * |*: // ] #ga #gb #H2f
  elim (IH â¦ Hg2 â¦ H1f â¦ H2f) -f -Hg2
  /3 width=11 by pr_sor_next_push, pr_sor_push_next, pr_sor_next_bi, ex3_2_intro, pr_coafter_refl, pr_coafter_push/
]
qed-.
