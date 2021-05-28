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

include "ground/relocation/gr_pat_tls.ma".
include "ground/relocation/gr_isf_tls.ma".
include "ground/relocation/gr_ist_tls.ma".
include "ground/relocation/gr_coafter_nat_tls.ma".
include "ground/relocation/gr_coafter_isi.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** H_coafter_isfin2_fwd *)
definition H_gr_coafter_des_ist_isf: predicate gr_map ≝
           λf1. ∀f2. 𝐅❪f2❫ → 𝐓❪f1❫ → ∀f. f1 ~⊚ f2 ≘ f →  𝐅❪f❫.

(* Forward lemmas with ist and isf *)

(*** coafter_isfin2_fwd_O_aux *)
fact gr_coafter_des_ist_isf_unit_aux:
     ∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_coafter_des_ist_isf f1.
#f1 #Hf1 #f2 #H
generalize in match Hf1; generalize in match f1; -f1
@(gr_isf_ind … H) -f2
[ /3 width=4 by gr_coafter_isi_inv_dx, gr_isf_isi/ ]
#f2 #_ #IH #f1 #H #Hf1 #f #Hf
elim (gr_pat_inv_unit_bi … H) -H [ |*: // ] #g1 #H1
lapply (gr_ist_inv_push … Hf1 … H1) -Hf1 #Hg1
elim (Hg1 (𝟏)) #n #Hn
[ elim (gr_coafter_inv_push_bi … Hf) | elim (gr_coafter_inv_push_next … Hf)
] -Hf [1,6: |*: // ] #g #Hg #H0 destruct
/5 width=6 by gr_isf_next, gr_isf_push, gr_isf_inv_tls, gr_ist_tls, gr_pat_unit_succ_tls, gr_coafter_tls_sn_tls/
qed-.

(*** coafter_isfin2_fwd_aux *)
fact gr_coafter_des_ist_isf_aux:
     (∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_coafter_des_ist_isf f1) →
     ∀i2,f1. @❪𝟏, f1❫ ≘ i2 → H_gr_coafter_des_ist_isf f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #f2 #Hf2 #H2f1 #f #Hf
elim (gr_pat_inv_unit_succ … H1f1) -H1f1 [ |*: // ] #g1 #Hg1 #H1
elim (gr_coafter_inv_next_sn … Hf … H1) -Hf #g #Hg #H0
lapply (IH … Hg1 … Hg) -i2 -Hg
/2 width=4 by gr_ist_inv_next, gr_isf_push/ (**) (* full auto fails *)
qed-.

(*** coafter_isfin2_fwd *)
lemma gr_coafter_des_ist_isf: ∀f1. H_gr_coafter_des_ist_isf f1.
#f1 #f2 #Hf2 #Hf1 cases (Hf1 (𝟏))
/3 width=7 by gr_coafter_des_ist_isf_aux, gr_coafter_des_ist_isf_unit_aux/
qed-.
