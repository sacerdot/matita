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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/unfold/lsstas_lift.ma".

(* NAT-ITERATED STRATIFIED STATIC TYPE ASSIGNMENT FOR TERMS *****************)

(* Main properties **********************************************************)

theorem lsstas_trans: ∀h,g,G,L. ltransitive … (lsstas h g G L).
/2 width=3 by lstar_ltransitive/ qed-.

theorem lsstas_mono: ∀h,g,G,L,l. singlevalued … (lsstas h g G L l).
/3 width=7 by ssta_mono, lstar_singlevalued/ qed-.

theorem lsstas_conf_le: ∀h,g,G,L,T,U1,l1. ⦃G, L⦄ ⊢ T •*[h, g, l1] U1 →
                        ∀U2,l2. l1 ≤ l2 →  ⦃G, L⦄ ⊢ T •*[h, g, l2] U2 →
                        ⦃G, L⦄ ⊢ U1 •*[h, g, l2 - l1] U2.
#h #g #G #L #T #U1 #l1 #HTU1 #U2 #l2 #Hl12
>(plus_minus_m_m … Hl12) in ⊢ (%→?); -Hl12 >commutative_plus #H
elim (lsstas_split … H) -H #U #HTU
>(lsstas_mono … HTU … HTU1) -T //
qed-.

(* Advanced properties ******************************************************)

lemma lsstas_ssta_conf_pos: ∀h,g,G,L,T,U1. ⦃G, L⦄ ⊢ T •[h, g] U1 →
                            ∀U2,l. ⦃G, L⦄ ⊢ T •*[h, g, l+1] U2 → ⦃G, L⦄ ⊢ U1 •*[h, g, l] U2.
#h #g #G #L #T #U1 #HTU1 #U2 #l #HTU2
lapply (lsstas_conf_le … T U1 1 … HTU2) -HTU2 // /2 width=1/
qed-.

lemma lsstas_strip_pos: ∀h,g,G,L,T1,U1. ⦃G, L⦄ ⊢ T1 •[h, g] U1 →
                        ∀T2,l. ⦃G, L⦄ ⊢ T1 •*[h, g, l+1] T2 →
                        ∃∃U2. ⦃G, L⦄ ⊢ T2 •[h, g] U2 & ⦃G, L⦄ ⊢ U1 •*[h, g, l+1] U2.
#h #g #G #L #T1 #U1 #HTU1 #T2 #l #HT12
elim (lsstas_fwd_correct … HTU1 … HT12)
lapply (lsstas_ssta_conf_pos … HTU1 … HT12) -T1 /3 width=5/
qed-.
