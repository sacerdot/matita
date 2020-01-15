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

include "basic_2/notation/relations/predtynormal_4.ma".
include "static_2/syntax/teqx.ma".
include "basic_2/rt_transition/cpx.ma".

(* NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ********)

definition cnx: ∀h. relation3 genv lenv term ≝
                λh,G,L. NF … (cpx h G L) teqx.

interpretation
   "normality for unbound context-sensitive parallel rt-transition (term)"
   'PRedTyNormal h G L T = (cnx h G L T).

(* Basic inversion lemmas ***************************************************)

lemma cnx_inv_abst: ∀h,p,G,L,V,T. ❪G,L❫ ⊢ ⬈𝐍[h] ⓛ[p]V.T →
                    ∧∧ ❪G,L❫ ⊢ ⬈𝐍[h] V & ❪G,L.ⓛV❫ ⊢ ⬈𝐍[h] T.
#h #p #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ[p]V2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2
| #T2 #HT2 lapply (HVT1 (ⓛ[p]V1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2
]
#H elim (teqx_inv_pair … H) -H //
qed-.

(* Basic_2A1: was: cnx_inv_abbr *)
lemma cnx_inv_abbr_neg: ∀h,G,L,V,T. ❪G,L❫ ⊢ ⬈𝐍[h] -ⓓV.T →
                        ∧∧ ❪G,L❫ ⊢ ⬈𝐍[h] V & ❪G,L.ⓓV❫ ⊢ ⬈𝐍[h] T.
#h #G #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2 by cpx_pair_sn/ -HV2
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2 by cpx_bind/ -HT2
]
#H elim (teqx_inv_pair … H) -H //
qed-.

(* Basic_2A1: was: cnx_inv_eps *)
lemma cnx_inv_cast: ∀h,G,L,V,T. ❪G,L❫ ⊢ ⬈𝐍[h] ⓝV.T → ⊥.
#h #G #L #V #T #H lapply (H T ?) -H
/2 width=6 by cpx_eps, teqx_inv_pair_xy_y/
qed-.

(* Basic properties *********************************************************)

lemma cnx_sort: ∀h,G,L,s. ❪G,L❫ ⊢ ⬈𝐍[h] ⋆s.
#h #G #L #s #X #H elim (cpx_inv_sort1 … H) -H
/2 width=1 by teqx_sort/
qed.

lemma cnx_abst: ∀h,p,G,L,W,T. ❪G,L❫ ⊢ ⬈𝐍[h] W → ❪G,L.ⓛW❫ ⊢ ⬈𝐍[h] T →
                ❪G,L❫ ⊢ ⬈𝐍[h] ⓛ[p]W.T.
#h #p #G #L #W #T #HW #HT #X #H
elim (cpx_inv_abst1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
@teqx_pair [ @HW | @HT ] // (**) (* auto fails because δ-expansion gets in the way *)
qed.
