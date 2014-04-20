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

include "basic_2/notation/relations/predstar_6.ma".
include "basic_2/reduction/cnx.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

definition cpxs: ∀h. sd h → relation4 genv lenv term term ≝
                 λh,g,G. LTC … (cpx h g G).

interpretation "extended context-sensitive parallel computation (term)"
   'PRedStar h g G L T1 T2 = (cpxs h g G L T1 T2).

(* Basic eliminators ********************************************************)

lemma cpxs_ind: ∀h,g,G,L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T → ⦃G, L⦄ ⊢ T ➡[h, g] T2 → R T → R T2) →
                ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → R T2.
#h #g #L #G #T1 #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cpxs_ind_dx: ∀h,g,G,L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. ⦃G, L⦄ ⊢ T1 ➡[h, g] T → ⦃G, L⦄ ⊢ T ➡*[h, g] T2 → R T → R T1) →
                   ∀T1. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → R T1.
#h #g #G #L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

lemma cpxs_refl: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ➡*[h, g] T.
/2 width=1 by inj/ qed.

lemma cpx_cpxs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
/2 width=1 by inj/ qed.

lemma cpxs_strap1: ∀h,g,G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ➡[h, g] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
normalize /2 width=3 by step/ qed.

lemma cpxs_strap2: ∀h,g,G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡[h, g] T →
                   ∀T2. ⦃G, L⦄ ⊢ T ➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
normalize /2 width=3 by TC_strap/ qed.

lemma lsubr_cpxs_trans: ∀h,g,G. lsub_trans … (cpxs h g G) lsubr.
/3 width=5 by lsubr_cpx_trans, LTC_lsub_trans/
qed-.

lemma cprs_cpxs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #H @(cprs_ind … H) -T2 /3 width=3 by cpxs_strap1, cpr_cpx/
qed.

lemma cpxs_bind_dx: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                    ∀I,T1,T2. ⦃G, L. ⓑ{I}V1⦄ ⊢ T1 ➡*[h, g] T2 →
                    ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
#h #g #G #L #V1 #V2 #HV12 #I #T1 #T2 #HT12 #a @(cpxs_ind_dx … HT12) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_pair_sn, cpx_bind/
qed.

lemma cpxs_flat_dx: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                    ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 →
                    ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h, g] ⓕ{I}V2.T2.
#h #g #G #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cpxs_ind … HT12) -T2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_flat_sn: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 →
                    ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                    ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h, g] ⓕ{I}V2.T2.
#h #g #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_strap1, cpx_cpxs, cpx_pair_sn, cpx_flat/
qed.

lemma cpxs_pair_sn: ∀h,g,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                    ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡*[h, g] ②{I}V2.T.
#h #g #I #G #L #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_pair_sn/
qed.

lemma cpxs_zeta: ∀h,g,G,L,V,T1,T,T2. ⇧[0, 1] T2 ≡ T →
                 ⦃G, L.ⓓV⦄ ⊢ T1 ➡*[h, g] T → ⦃G, L⦄ ⊢ +ⓓV.T1 ➡*[h, g] T2.
#h #g #G #L #V #T1 #T #T2 #HT2 #H @(cpxs_ind_dx … H) -T1
/3 width=3 by cpxs_strap2, cpx_cpxs, cpx_bind, cpx_zeta/
qed.

lemma cpxs_eps: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 →
                ∀V. ⦃G, L⦄ ⊢ ⓝV.T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_eps/
qed.

lemma cpxs_ct: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
               ∀T. ⦃G, L⦄ ⊢ ⓝV1.T ➡*[h, g] V2.
#h #g #G #L #V1 #V2 #H @(cpxs_ind … H) -V2
/3 width=3 by cpxs_strap1, cpx_cpxs, cpx_ct/
qed.

lemma cpxs_beta_dx: ∀h,g,a,G,L,V1,V2,W1,W2,T1,T2.
                    ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 →
                    ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[h, g] ⓓ{a}ⓝW2.V2.T2.
#h #g #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 * -T2
/4 width=7 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_beta/
qed.

lemma cpxs_theta_dx: ∀h,g,a,G,L,V1,V,V2,W1,W2,T1,T2.
                     ⦃G, L⦄ ⊢ V1 ➡[h, g] V → ⇧[0, 1] V ≡ V2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[h, g] T2 →
                     ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 → ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[h, g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2 
/4 width=9 by cpx_cpxs, cpxs_strap1, cpxs_bind_dx, cpxs_flat_dx, cpx_theta/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpxs_inv_sort1: ∀h,g,G,L,U2,k. ⦃G, L⦄ ⊢ ⋆k ➡*[h, g] U2 →
                      ∃∃n,l. deg h g k (n+l) & U2 = ⋆((next h)^n k).
#h #g #G #L #U2 #k #H @(cpxs_ind … H) -U2
[ elim (deg_total h g k) #l #Hkl
  @(ex2_2_intro … 0 … Hkl) -Hkl //
| #U #U2 #_ #HU2 * #n #l #Hknl #H destruct
  elim (cpx_inv_sort1 … HU2) -HU2
  [ #H destruct /2 width=4 by ex2_2_intro/
  | * #l0 #Hkl0 #H destruct -l
    @(ex2_2_intro … (n+1) l0) /2 width=1 by deg_inv_prec/ >iter_SO //
  ]
]
qed-.

lemma cpxs_inv_cast1: ∀h,g,G,L,W1,T1,U2. ⦃G, L⦄ ⊢ ⓝW1.T1 ➡*[h, g] U2 →
                      ∨∨ ∃∃W2,T2. ⦃G, L⦄ ⊢ W1 ➡*[h, g] W2 & ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 & U2 = ⓝW2.T2
                       | ⦃G, L⦄ ⊢ T1 ➡*[h, g] U2
                       | ⦃G, L⦄ ⊢ W1 ➡*[h, g] U2.
#h #g #G #L #W1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5 by or3_intro0, ex3_2_intro/
#U2 #U #_ #HU2 * /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W #T #HW1 #HT1 #H destruct
elim (cpx_inv_cast1 … HU2) -HU2 /3 width=3 by cpxs_strap1, or3_intro1, or3_intro2/ *
#W2 #T2 #HW2 #HT2 #H destruct
lapply (cpxs_strap1 … HW1 … HW2) -W
lapply (cpxs_strap1 … HT1 … HT2) -T /3 width=5 by or3_intro0, ex3_2_intro/
qed-.

lemma cpxs_inv_cnx1: ∀h,g,G,L,T,U. ⦃G, L⦄ ⊢ T ➡*[h, g] U → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → T = U.
#h #g #G #L #T #U #H @(cpxs_ind_dx … H) -T //
#T0 #T #H1T0 #_ #IHT #H2T0
lapply (H2T0 … H1T0) -H1T0 #H destruct /2 width=1 by/
qed-.

lemma cpxs_neq_inv_step_sn: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → (T1 = T2 → ⊥) →
                            ∃∃T. ⦃G, L⦄ ⊢ T1 ➡[h, g] T & T1 = T → ⊥ & ⦃G, L⦄ ⊢ T ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #H @(cpxs_ind_dx … H) -T1
[ #H elim H -H //
| #T1 #T #H1 #H2 #IH2 #H12 elim (eq_term_dec T1 T) #H destruct
  [ -H1 -H2 /3 width=1 by/
  | -IH2 /3 width=4 by ex3_intro/ (**) (* auto fails without clear *)
  ]
]
qed-.
