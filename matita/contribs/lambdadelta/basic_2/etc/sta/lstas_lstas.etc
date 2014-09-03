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

include "basic_2/static/sta_sta.ma".
include "basic_2/unfold/lstas_lift.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Main properties **********************************************************)

theorem lstas_trans: ∀h,G,L. ltransitive … (lstas h G L).
/2 width=3 by lstar_ltransitive/ qed-.

theorem lstas_mono: ∀h,G,L,l. singlevalued … (lstas h G L l).
/3 width=7 by sta_mono, lstar_singlevalued/ qed-.

theorem lstas_conf_le: ∀h,G,L,T,U1,l1. ⦃G, L⦄ ⊢ T •*[h, l1] U1 →
                       ∀U2,l2. l1 ≤ l2 → ⦃G, L⦄ ⊢ T •*[h, l2] U2 →
                       ⦃G, L⦄ ⊢ U1 •*[h, l2-l1] U2.
#h #G #L #T #U1 #l1 #HTU1 #U2 #l2 #Hl12
>(plus_minus_m_m … Hl12) in ⊢ (%→?); -Hl12 >commutative_plus #H
elim (lstas_split … H) -H #U #HTU
>(lstas_mono … HTU … HTU1) -T //
qed-.

(* Advanced properties ******************************************************)

lemma lstas_sta_conf_pos: ∀h,G,L,T,U1. ⦃G, L⦄ ⊢ T •[h] U1 →
                          ∀U2,l. ⦃G, L⦄ ⊢ T •*[h, l+1] U2 → ⦃G, L⦄ ⊢ U1 •*[h, l] U2.
#h #G #L #T #U1 #HTU1 #U2 #l #HTU2
lapply (lstas_conf_le … T U1 1 … HTU2) -HTU2 /2 width=1 by sta_lstas/
qed-.

lemma lstas_strip_pos: ∀h,G,L,T1,U1. ⦃G, L⦄ ⊢ T1 •[h] U1 →
                       ∀T2,l. ⦃G, L⦄ ⊢ T1 •*[h, l+1] T2 →
                       ∃∃U2. ⦃G, L⦄ ⊢ T2 •[h] U2 & ⦃G, L⦄ ⊢ U1 •*[h, l+1] U2.
#h #G #L #T1 #U1 #HTU1 #T2 #l #HT12
elim (lstas_fwd_correct … HTU1 … HT12)
lapply (lstas_sta_conf_pos … HTU1 … HT12) -T1 /3 width=5 by lstas_step_dx, ex2_intro/
qed-.
