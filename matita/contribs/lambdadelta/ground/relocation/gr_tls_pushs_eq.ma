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

include "ground/relocation/gr_tls_eq.ma".
include "ground/relocation/gr_pushs.ma".

(* ITERATED TAIL FOR GENERIC RELOCATION MAPS ********************************)

(* Inversions with gr_pushs and gr_eq ***************************************)

(*** eq_inv_pushs_sn *)
lemma gr_eq_inv_pushs_sn (n):
      ∀f1,g2. ⫯*[n] f1 ≡ g2 →
      ∧∧ f1 ≡ ⫱*[n]g2 & ⫯*[n]⫱*[n]g2 = g2.
#n @(nat_ind_succ … n) -n /2 width=1 by conj/
#n #IH #f1 #g2 #H
elim (gr_eq_inv_push_sn … H) -H [|*: // ] #Hf10 *
elim (IH … Hf10) -IH -Hf10 #Hf12 #H1
/2 width=1 by conj/
qed-.

(*** eq_inv_pushs_dx *)
lemma gr_eq_inv_pushs_dx (n):
      ∀f2,g1. g1 ≡ ⫯*[n] f2 →
      ∧∧ ⫱*[n]g1 ≡ f2 & ⫯*[n]⫱*[n]g1 = g1.
#n @(nat_ind_succ … n) -n /2 width=1 by conj/
#n #IH #f2 #g1 #H
elim (gr_eq_inv_push_dx … H) -H [|*: // ] #Hf02 *
elim (IH … Hf02) -IH -Hf02 #Hf12 #H2
/2 width=1 by conj/
qed-.
