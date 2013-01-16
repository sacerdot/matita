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

include "paths/standard_trace.ma".
include "paths/labeled_sequential_computation.ma".
include "paths/labeled_st_reduction.ma".

(* PATH-LABELED STANDARD COMPUTATION (MULTISTEP) ****************************)

(* Note: lstar shuld be replaced by l_sreds *)
definition pl_sts: trace → relation subterms ≝ lstar … pl_st.

interpretation "path-labeled standard reduction"
    'StdStar F p G = (pl_sts p F G).

notation "hvbox( F break Ⓡ ↦* [ term 46 p ] break term 46 G )"
   non associative with precedence 45
   for @{ 'StdStar $F $p $G }.

lemma pl_sts_fwd_pl_sreds: ∀s,F1,F2. F1 Ⓡ↦*[s] F2 → ⇓F1 ↦*[s] ⇓F2.
#s #F1 #F2 #H @(lstar_ind_r … s F2 H) -s -F2 //
#p #s #F #F2 #_ #HF2 #IHF1
lapply (pl_st_fwd_pl_sred … HF2) -HF2 /2 width=3/
qed-.

lemma pl_sts_inv_pl_sreds: ∀s,M1,F2. {⊤}⇑M1 Ⓡ↦*[s] F2 → is_whd s →
                           ∃∃M2. M1 ↦*[s] M2 & {⊤}⇑M2 = F2.
#s #M1 #F2 #H @(lstar_ind_r … s F2 H) -s -F2 /2 width=3/
#p #s #F #F2 #_ #HF2 #IHF #H
elim (is_whd_inv_append … H) -H #Hs * #Hp #_
elim (IHF Hs) -IHF -Hs #M #HM #H destruct
elim (pl_st_inv_pl_sred … HF2) -HF2 // -Hp #M2 #HM2 #H
lapply (pl_sreds_step_dx … HM … HM2) -M /2 width=3/
qed-.

lemma pl_sts_refl: reflexive … (pl_sts (◊)).
//
qed.

lemma pl_sts_step_sn: ∀p,F1,F. F1 Ⓡ↦[p] F → ∀s,F2. F Ⓡ↦*[s] F2 → F1 Ⓡ↦*[p::s] F2.
/2 width=3/
qed-.

lemma pl_sts_step_dx: ∀s,F1,F. F1 Ⓡ↦*[s] F → ∀p,F2. F Ⓡ↦[p] F2 → F1 Ⓡ↦*[s@p::◊] F2.
/2 width=3/
qed-.

lemma pl_sts_step_rc: ∀p,F1,F2. F1 Ⓡ↦[p] F2 → F1 Ⓡ↦*[p::◊] F2.
/2 width=1/
qed.

lemma pl_sts_inv_nil: ∀s,F1,F2. F1 Ⓡ↦*[s] F2 → ◊ = s → F1 = F2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma pl_sts_inv_cons: ∀s,F1,F2. F1 Ⓡ↦*[s] F2 → ∀q,r. q::r = s →
                       ∃∃F. F1 Ⓡ↦[q] F & F Ⓡ↦*[r] F2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma pl_sts_inv_step_rc: ∀p,F1,F2. F1 Ⓡ↦*[p::◊] F2 → F1 Ⓡ↦[p] F2.
/2 width=1 by lstar_inv_step/
qed-.

lemma pl_sts_inv_pos: ∀s,F1,F2. F1 Ⓡ↦*[s] F2 → 0 < |s| →
                      ∃∃p,r,F. p::r = s & F1 Ⓡ↦[p] F & F Ⓡ↦*[r] F2.
/2 width=1 by lstar_inv_pos/
qed-.

lemma pl_sts_lift: ∀s. sliftable (pl_sts s).
/2 width=1/
qed.

lemma pl_sts_inv_lift: ∀s. sdeliftable_sn (pl_sts s).
/3 width=3 by lstar_sdeliftable_sn, pl_st_inv_lift/
qed-.

lemma pl_sts_dsubst: ∀s. sdsubstable_f_dx … (booleanized ⊥) (pl_sts s).
/2 width=1/
qed.

theorem pl_sts_mono: ∀s. singlevalued … (pl_sts s).
/3 width=7 by lstar_singlevalued, pl_st_mono/
qed-.

theorem pl_sts_trans: ltransitive … pl_sts.
/2 width=3 by lstar_ltransitive/
qed-.

theorem pl_sts_fwd_is_standard: ∀s,F1,F2. F1 Ⓡ↦*[s] F2 → is_standard s.
#s elim s -s // #p1 * //
#p2 #s #IHs #F1 #F2 #H
elim (pl_sts_inv_cons … H ???) -H [4: // |2,3: skip ] #F3 #HF13 #H (**) (* simplify line *)
elim (pl_sts_inv_cons … H ???) [2: // |3,4: skip ] #F4 #HF34 #_ (**) (* simplify line *)
lapply (pl_st_fwd_sle … HF13 … HF34) -F1 -F4 /3 width=3/
qed-.

axiom pl_sred_is_standard_pl_st: ∀p,M,M2. M ↦[p] M2 → ∀F. ⇓F = M →
                                 ∀s,M1.{⊤}⇑ M1 Ⓡ↦*[s] F →
                                 is_standard (s@(p::◊)) →
                                 ∃∃F2. F Ⓡ↦[p] F2 & ⇓F2 = M2.
(*
#p #M #M2 #H elim H -p -M -M2
[ #B #A #F #HF #s #M1 #HM1 #Hs
  lapply (is_standard_fwd_is_whd … Hs) -Hs // #Hs
  elim (pl_sts_inv_pl_sreds … HM1 Hs) -HM1 -Hs #M #_ #H -s -M1 destruct
  >carrier_boolean in HF; #H destruct normalize /2 width=3/
| #p #A1 #A2 #_ #IHA12 #F #HF #s #M1 #HM1 #Hs
  elim (carrier_inv_abst … HF) -HF #b #T #HT #HF destruct
(*  
  elim (carrier_inv_appl … HF) -HF #b1 #V #G #HV #HG #HF
*)  
*)
theorem pl_sreds_is_standard_pl_sts: ∀s,M1,M2. M1 ↦*[s] M2 → is_standard s →
                                     ∃∃F2. {⊤}⇑ M1 Ⓡ↦*[s] F2 & ⇓F2 = M2.
#s #M1 #M2 #H @(lstar_ind_r … s M2 H) -s -M2 /2 width=3/
#p #s #M #M2 #_ #HM2 #IHM1 #Hsp
lapply (is_standard_fwd_append_sn … Hsp) #Hs
elim (IHM1 Hs) -IHM1 -Hs #F #HM1 #H
elim (pl_sred_is_standard_pl_st … HM2 … HM1 ?) -HM2 // -M -Hsp #F2 #HF2 #HFM2
lapply (pl_sts_step_dx … HM1 … HF2) -F
#H @(ex2_intro … F2) // (**) (* auto needs some help here *)
qed-.
