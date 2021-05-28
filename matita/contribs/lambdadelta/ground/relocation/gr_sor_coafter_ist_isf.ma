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

include "ground/relocation/gr_isf.ma".
include "ground/relocation/gr_coafter_isi.ma".
include "ground/relocation/gr_coafter_ist_isi.ma".
include "ground/relocation/gr_sor_isi.ma".

(* RELATIONAL UNION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with coafter and ist and isf ****************************************************)

(*** coafter_sor *)
lemma gr_sor_coafter_dx_tans:
      ∀f. 𝐅❪f❫ → ∀f2. 𝐓❪f2❫ → ∀f1. f2 ~⊚ f1 ≘ f → ∀f1a,f1b. f1a ⋓ f1b ≘ f1 →
      ∃∃fa,fb. f2 ~⊚ f1a ≘ fa & f2 ~⊚ f1b ≘ fb & fa ⋓ fb ≘ f.
@gr_isf_ind
[ #f #Hf #f2 #Hf2 #f1 #Hf #f1a #f1b #Hf1
  lapply (gr_coafter_des_ist_sn_isi … Hf ??) -Hf // #H2f1
  elim (gr_sor_inv_isi … Hf1) -Hf1 //
  /3 width=5 by gr_coafter_isi_dx, gr_sor_idem, ex3_2_intro/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (gr_coafter_inv_push … H1) -H1 [1,3: * |*: // ]
  [ #g2 #g1 #Hf #Hgf2 #Hgf1
    elim (gr_sor_inv_push … H2) -H2 [ |*: // ] #ga #gb #Hg1
    lapply (gr_ist_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
    elim (IH … Hf … Hg1) // -f1 -g1 -IH -Hg2
    /3 width=11 by gr_coafter_refl, gr_sor_push_bi, ex3_2_intro/
  | #g2 #Hf #Hgf2
    lapply (gr_ist_inv_next … Hf2 … Hgf2) -Hf2 #Hg2
    elim (IH … Hf … H2) // -f1 -IH -Hg2
    /3 width=11 by gr_coafter_next, gr_sor_push_bi, ex3_2_intro/
  ]
| #f #_ #IH #f2 #Hf2 #f1 #H1 #f1a #f1b #H2
  elim (gr_coafter_inv_next … H1) -H1 [ |*: // ] #g2 #g1 #Hf #Hgf2 #Hgf1
  lapply (gr_ist_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
  elim (gr_sor_inv_next … H2) -H2 [1,3,4: * |*: // ] #ga #gb #Hg1
  elim (IH … Hf … Hg1) // -f1 -g1 -IH -Hg2
  /3 width=11 by gr_coafter_refl, gr_coafter_push, gr_sor_next_push, gr_sor_push_next, gr_sor_next_bi, ex3_2_intro/
]
qed-.

(*** coafter_inv_sor *)
lemma gr_sor_coafter_div:
      ∀f. 𝐅❪f❫ → ∀f2. 𝐓❪f2❫ → ∀f1. f2 ~⊚ f1 ≘ f → ∀fa,fb. fa ⋓ fb ≘ f →
      ∃∃f1a,f1b. f2 ~⊚ f1a ≘ fa & f2 ~⊚ f1b ≘ fb & f1a ⋓ f1b ≘ f1.
@gr_isf_ind
[ #f #Hf #f2 #Hf2 #f1 #H1f #fa #fb #H2f
  elim (gr_sor_inv_isi … H2f) -H2f //
  lapply (gr_coafter_des_ist_sn_isi … H1f ??) -H1f //
  /3 width=5 by ex3_2_intro, gr_coafter_isi_dx, gr_sor_isi_bi_isi/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (gr_sor_inv_push … H2) -H2 [ |*: // ] #ga #gb #H2f
  elim (gr_coafter_inv_push … H1) -H1 [1,3: * |*: // ] #g2 [ #g1 ] #H1f #Hgf2
  [ lapply (gr_ist_inv_push … Hf2 … Hgf2) | lapply (gr_ist_inv_next … Hf2 … Hgf2) ] -Hf2 #Hg2
  elim (IH … Hg2 … H1f … H2f) -f -Hg2
  /3 width=11 by gr_sor_push_bi, ex3_2_intro, gr_coafter_refl, gr_coafter_next/
| #f #_ #IH #f2 #Hf2 #f1 #H1 #fa #fb #H2
  elim (gr_coafter_inv_next … H1) -H1 [ |*: // ] #g2 #g1 #H1f #Hgf2
  lapply (gr_ist_inv_push … Hf2 … Hgf2) -Hf2 #Hg2
  elim (gr_sor_inv_next … H2) -H2 [1,3,4: * |*: // ] #ga #gb #H2f
  elim (IH … Hg2 … H1f … H2f) -f -Hg2
  /3 width=11 by gr_sor_next_push, gr_sor_push_next, gr_sor_next_bi, ex3_2_intro, gr_coafter_refl, gr_coafter_push/
]
qed-.
