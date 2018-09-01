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

include "basic_2/notation/relations/predtynormal_5.ma".
include "static_2/syntax/tdeq.ma".
include "basic_2/rt_transition/cpx.ma".

(* NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ********)

definition cnx: ∀h. sd h → relation3 genv lenv term ≝
                λh,o,G,L. NF … (cpx h G L) (tdeq h o …).

interpretation
   "normality for unbound context-sensitive parallel rt-transition (term)"
   'PRedTyNormal h o G L T = (cnx h o G L T).

(* Basic inversion lemmas ***************************************************)

lemma cnx_inv_sort: ∀h,o,G,L,s. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃⋆s⦄ → deg h o s 0.
#h #o #G #L #s #H
lapply (H (⋆(next h s)) ?) -H /2 width=2 by cpx_ess/ -G -L #H
elim (tdeq_inv_sort1 … H) -H #s0 #d #H1 #H2 #H destruct
lapply (deg_next … H1) #H0
lapply (deg_mono … H0 … H2) -H0 -H2 #H
>(pred_inv_fix_sn … H) -H //
qed-.

lemma cnx_inv_abst: ∀h,o,p,G,L,V,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃ⓛ{p}V.T⦄ →
                    ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃V⦄ ∧ ⦃G, L.ⓛV⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄.
#h #o #p #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ{p}V2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2
| #T2 #HT2 lapply (HVT1 (ⓛ{p}V1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2
]
#H elim (tdeq_inv_pair … H) -H //
qed-.

(* Basic_2A1: was: cnx_inv_abbr *)
lemma cnx_inv_abbr_neg: ∀h,o,G,L,V,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃-ⓓV.T⦄ →
                        ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃V⦄ ∧ ⦃G, L.ⓓV⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄.
#h #o #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2 
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2
]
#H elim (tdeq_inv_pair … H) -H //
qed-.

(* Basic_2A1: was: cnx_inv_eps *)
lemma cnx_inv_cast: ∀h,o,G,L,V,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃ⓝV.T⦄ → ⊥.
#h #o #G #L #V #T #H lapply (H T ?) -H
/2 width=6 by cpx_eps, tdeq_inv_pair_xy_y/
qed-.

(* Basic properties *********************************************************)

lemma cnx_sort: ∀h,o,G,L,s. deg h o s 0 → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃⋆s⦄.
#h #o #G #L #s #Hs #X #H elim (cpx_inv_sort1 … H) -H
/3 width=3 by tdeq_sort, deg_next/
qed.

lemma cnx_sort_iter: ∀h,o,G,L,s,d. deg h o s d → ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃⋆((next h)^d s)⦄.
#h #o #G #L #s #d #Hs lapply (deg_iter … d Hs) -Hs
<minus_n_n /2 width=6 by cnx_sort/
qed.

lemma cnx_abst: ∀h,o,p,G,L,W,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃W⦄ → ⦃G, L.ⓛW⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄ →
                ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃ⓛ{p}W.T⦄.
#h #o #p #G #L #W #T #HW #HT #X #H
elim (cpx_inv_abst1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
@tdeq_pair [ @HW | @HT ] // (**) (* auto fails because δ-expansion gets in the way *)
qed.
