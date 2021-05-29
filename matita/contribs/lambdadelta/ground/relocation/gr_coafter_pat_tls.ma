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
include "ground/relocation/gr_coafter_nat_tls.ma".

(* RELATIONAL CO-COMPOSITION FOR GENERIC RELOCATION MAPS ********************)

(* Constructions with gr_pat and gr_tls *************************************)

(* Note: this does not require ↑ first and second j *)
(*** coafter_tls_succ *)
lemma gr_coafter_tls_tl_tls:
      ∀g2,g1,g. g2 ~⊚ g1 ≘ g →
      ∀j. @❪𝟏, g2❫ ≘ j → ⫱*[j]g2 ~⊚ ⫱g1 ≘ ⫱*[j]g.
#g2 #g1 #g #Hg #j #Hg2
lapply (gr_nat_pred_bi … Hg2) -Hg2 #Hg2
lapply (gr_coafter_tls_bi_tls … Hg2 … Hg) -Hg #Hg
lapply (gr_pat_unit_succ_tls … Hg2) -Hg2 #H
elim (gr_pat_inv_unit_bi … H) -H [ |*: // ] #f2 #H2
elim (gr_coafter_inv_push_sn … Hg … H2) -Hg * #f1 #f #Hf #H1 #H0
>(npsucc_pred j) <gr_tls_succ <gr_tls_succ //
qed.

(* Note: parked for now
lemma coafter_fwd_xpx_pushs:
      ∀g2,f1,g,i,j. @❪i, g2❫ ≘ j → g2 ~⊚ ⫯*[i]⫯f1 ≘ g →
      ∃∃f.  ⫱*[↑j]g2 ~⊚ f1 ≘ f & ⫯*[j]⫯f = g.
#g2 #g1 #g #i #j #Hg2 <pushs_xn #Hg(coafter_fwd_pushs … Hg Hg2) #f #H0 destruct
lapply (coafter_tls … Hg2 Hg) -Hg <tls_pushs <tls_pushs #Hf
lapply (at_inv_tls … Hg2) -Hg2 #H
lapply (coafter_eq_repl_fwd2 … Hf … H) -H -Hf #Hf
elim (coafter_inv_ppx … Hf) [|*: // ] -Hf #g #Hg #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma coafter_fwd_xnx_pushs:
      ∀g2,f1,g,i,j. @❪i, g2❫ ≘ j → g2 ~⊚ ⫯*[i]↑f1 ≘ g →
      ∃∃f. ⫱*[↑j]g2 ~⊚ f1 ≘ f & ⫯*[j] ↑f = g.
#g2 #g1 #g #i #j #Hg2 #Hg
elim (coafter_fwd_pushs … Hg Hg2) #f #H0 destruct
lapply (coafter_tls … Hg2 Hg) -Hg <tls_pushs <tls_pushs #Hf
lapply (at_inv_tls … Hg2) -Hg2 #H
lapply (coafter_eq_repl_fwd2 … Hf … H) -H -Hf #Hf
elim (coafter_inv_pnx … Hf) [|*: // ] -Hf #g #Hg #H destruct
/2 width=3 by ex2_intro/
qed-.
*)
