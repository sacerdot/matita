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
include "ground/relocation/gr_isi_tls.ma".
include "ground/relocation/gr_ist_tls.ma".
include "ground/relocation/gr_coafter_nat_tls.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(*** H_coafter_fwd_isid2 *)
definition H_gr_coafter_des_ist_sn_isi: predicate gr_map ≝
           λf1. ∀f2,f. f1 ~⊚ f2 ≘ f → 𝐓❪f1❫ → 𝐈❪f❫ → 𝐈❪f2❫.

(* Forward lemmas with ist and isi *)

(*** coafter_fwd_isid2_O_aux *)
corec fact gr_coafter_des_ist_sn_isi_unit_aux:
           ∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_coafter_des_ist_sn_isi f1.
#f1 #H1f1 #f2 #f #H #H2f1 #Hf
cases (gr_pat_inv_unit_bi … H1f1) -H1f1 [ |*: // ] #g1 #H1
lapply (gr_ist_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 (𝟏)) #n #Hn
cases (gr_coafter_inv_push_sn … H … H1) -H * #g2 #g #H #H2 #H0
[ lapply (gr_isi_inv_push … Hf … H0) -Hf #Hg
  @(gr_isi_push … H2) -H2
  /3 width=7 by gr_coafter_tls_sn_tls, gr_pat_unit_succ_tls, gr_ist_tls, gr_isi_tls/
| cases (gr_isi_inv_next … Hf … H0)
]
qed-.

(*** coafter_fwd_isid2_aux *)
fact gr_coafter_des_ist_sn_isi_aux:
     (∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_coafter_des_ist_sn_isi f1) →
     ∀i2,f1. @❪𝟏, f1❫ ≘ i2 → H_gr_coafter_des_ist_sn_isi f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #f2 #f #H #H2f1 #Hf
elim (gr_pat_inv_unit_succ … H1f1) -H1f1 [ |*: // ] #g1 #Hg1 #H1
elim (gr_coafter_inv_next_sn … H … H1) -H #g #Hg #H0
@(IH … Hg1 … Hg) /2 width=3 by gr_ist_inv_next, gr_isi_inv_push/ (**) (* full auto fails *)
qed-.

(*** coafter_fwd_isid2 *)
lemma gr_coafter_des_ist_sn_isi:
      ∀f1. H_gr_coafter_des_ist_sn_isi f1.
#f1 #f2 #f #Hf #H cases (H (𝟏))
/3 width=7 by gr_coafter_des_ist_sn_isi_aux, gr_coafter_des_ist_sn_isi_unit_aux/
qed-.
