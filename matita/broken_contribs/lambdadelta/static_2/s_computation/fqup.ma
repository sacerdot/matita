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

include "ground/lib/star.ma".
include "static_2/notation/relations/suptermplus_6.ma".
include "static_2/notation/relations/suptermplus_7.ma".
include "static_2/s_transition/fqu.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

definition fqup: bool → tri_relation genv lenv term ≝
                 λb. tri_TC … (fqu b).

interpretation "extended plus-iterated structural successor (closure)"
   'SupTermPlus b G1 L1 T1 G2 L2 T2 = (fqup b G1 L1 T1 G2 L2 T2).

interpretation "plus-iterated structural successor (closure)"
   'SupTermPlus G1 L1 T1 G2 L2 T2 = (fqup true G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_fqup: ∀b,G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ⬂[b] ❨G2,L2,T2❩ →
                ❨G1,L1,T1❩ ⬂+[b] ❨G2,L2,T2❩.
/2 width=1 by tri_inj/ qed.

lemma fqup_strap1: ∀b,G1,G,G2,L1,L,L2,T1,T,T2.
                   ❨G1,L1,T1❩ ⬂+[b] ❨G,L,T❩ → ❨G,L,T❩ ⬂[b] ❨G2,L2,T2❩ →
                   ❨G1,L1,T1❩ ⬂+[b] ❨G2,L2,T2❩.
/2 width=5 by tri_step/ qed.

lemma fqup_strap2: ∀b,G1,G,G2,L1,L,L2,T1,T,T2.
                   ❨G1,L1,T1❩ ⬂[b] ❨G,L,T❩ → ❨G,L,T❩ ⬂+[b] ❨G2,L2,T2❩ →
                   ❨G1,L1,T1❩ ⬂+[b] ❨G2,L2,T2❩.
/2 width=5 by tri_TC_strap/ qed.

lemma fqup_pair_sn: ∀b,I,G,L,V,T. ❨G,L,②[I]V.T❩ ⬂+[b] ❨G,L,V❩.
/2 width=1 by fqu_pair_sn, fqu_fqup/ qed.

lemma fqup_bind_dx: ∀p,I,G,L,V,T. ❨G,L,ⓑ[p,I]V.T❩ ⬂+[ⓣ] ❨G,L.ⓑ[I]V,T❩.
/3 width=1 by fqu_bind_dx, fqu_fqup/ qed.

lemma fqup_clear: ∀p,I,G,L,V,T. ❨G,L,ⓑ[p,I]V.T❩ ⬂+[ⓕ] ❨G,L.ⓧ,T❩.
/3 width=1 by fqu_clear, fqu_fqup/ qed.

lemma fqup_flat_dx: ∀b,I,G,L,V,T. ❨G,L,ⓕ[I]V.T❩ ⬂+[b] ❨G,L,T❩.
/2 width=1 by fqu_flat_dx, fqu_fqup/ qed.

lemma fqup_flat_dx_pair_sn: ∀b,I1,I2,G,L,V1,V2,T. ❨G,L,ⓕ[I1]V1.②[I2]V2.T❩ ⬂+[b] ❨G,L,V2❩.
/2 width=5 by fqu_pair_sn, fqup_strap1/ qed.

lemma fqup_bind_dx_flat_dx: ∀p,G,I1,I2,L,V1,V2,T. ❨G,L,ⓑ[p,I1]V1.ⓕ[I2]V2.T❩ ⬂+[ⓣ] ❨G,L.ⓑ[I1]V1,T❩.
/2 width=5 by fqu_flat_dx, fqup_strap1/ qed.

lemma fqup_flat_dx_bind_dx: ∀p,I1,I2,G,L,V1,V2,T. ❨G,L,ⓕ[I1]V1.ⓑ[p,I2]V2.T❩ ⬂+[ⓣ] ❨G,L.ⓑ[I2]V2,T❩.
/3 width=5 by fqu_bind_dx, fqup_strap1/ qed.

(* Basic eliminators ********************************************************)

lemma fqup_ind: ∀b,G1,L1,T1. ∀Q:relation3 ….
                (∀G2,L2,T2. ❨G1,L1,T1❩ ⬂[b] ❨G2,L2,T2❩ → Q G2 L2 T2) →
                (∀G,G2,L,L2,T,T2. ❨G1,L1,T1❩ ⬂+[b] ❨G,L,T❩ → ❨G,L,T❩ ⬂[b] ❨G2,L2,T2❩ → Q G L T → Q G2 L2 T2) →
                ∀G2,L2,T2. ❨G1,L1,T1❩ ⬂+[b] ❨G2,L2,T2❩ → Q G2 L2 T2.
#b #G1 #L1 #T1 #Q #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_ind … IH1 IH2 G2 L2 T2 H)
qed-.

lemma fqup_ind_dx: ∀b,G2,L2,T2. ∀Q:relation3 ….
                   (∀G1,L1,T1. ❨G1,L1,T1❩ ⬂[b] ❨G2,L2,T2❩ → Q G1 L1 T1) →
                   (∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ⬂[b] ❨G,L,T❩ → ❨G,L,T❩ ⬂+[b] ❨G2,L2,T2❩ → Q G L T → Q G1 L1 T1) →
                   ∀G1,L1,T1. ❨G1,L1,T1❩ ⬂+[b] ❨G2,L2,T2❩ → Q G1 L1 T1.
#b #G2 #L2 #T2 #Q #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_ind_dx … IH1 IH2 G1 L1 T1 H)
qed-.

(* Advanced properties ******************************************************)

lemma fqup_zeta (b) (p) (I) (G) (K) (V):
                ∀T1,T2. ⇧[⁤𝟏]T2 ≘ T1 → ❨G,K,ⓑ[p,I]V.T1❩ ⬂+[b] ❨G,K,T2❩.
* /4 width=5 by fqup_strap2, fqu_fqup, fqu_drop, fqu_clear, fqu_bind_dx/ qed.

(* Basic_2A1: removed theorems 1: fqup_drop *)
