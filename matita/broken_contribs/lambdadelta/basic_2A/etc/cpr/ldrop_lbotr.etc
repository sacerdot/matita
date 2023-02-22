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

include "basic_2/relocation/lsubr_lbotr.ma".
include "basic_2/relocation/ldrop_ldrop.ma".

(* DROPPING *****************************************************************)

(* Inversion lemmas about local env. full refinement for substitution *******)

(* Note: ldrop_ldrop not needed *)
lemma lbotr_inv_ldrop: ∀I,L,K,V,i. ⇩[0, i] L ≡ K. ⓑ{I}V → ∀d,e. ⊒[d, e] L →
                       d ≤ i → i < d + e → I = Abbr.
#I #L elim L -L
[ #K #V #i #H
  lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L #J #W #IHL #K #V #i #H
  elim (ldrop_inv_O1 … H) -H *
  [ -IHL #H1 #H2 #d #e #HL #Hdi #Hide destruct
    lapply (le_n_O_to_eq … Hdi) -Hdi #H destruct
    lapply (HL … (L.ⓓW) ?) -HL /2 width=1/ #H
    elim (lsubr_inv_abbr2 … H ?) -H // -Hide #K #_ #H destruct //
  | #Hi #HLK #d @(nat_ind_plus … d) -d
    [ #e #H #_ #Hide
      elim (lbotr_inv_bind … H ?) -H [2: /2 width=2/ ] #HL #H destruct
      @(IHL … HLK … HL) -IHL -HLK -HL // /2 width=1/
    | #d #_ #e #H #Hdi #Hide
      lapply (lbotr_inv_skip … H ?) -H // #HL
      @(IHL … HLK … HL) -IHL -HLK -HL /2 width=1/
    ]
  ]
]
qed-.

(* Properties about local env. full refinement for substitution *************)

(* Note: ldrop_ldrop not needed *)
lemma lbotr_ldrop: ∀L,d,e.
                   (∀I,K,V,i. d ≤ i → i < d + e → ⇩[0, i] L ≡ K. ⓑ{I}V → I = Abbr) →
                   ⊒[d, e] L.
#L elim L -L //
#L #I #V #IHL #d @(nat_ind_plus … d) -d
[ #e @(nat_ind_plus … e) -e //
  #e #_ #H0
  >(H0 I L V 0 ? ? ?) //
  /5 width=6 by lbotr_abbr, ldrop_ldrop, lt_minus_to_plus_r/ (**) (* auto now too slow without trace *)
| #d #_ #e #H0
  /5 width=6 by lbotr_skip, ldrop_ldrop, le_S_S, lt_minus_to_plus_r/ (**) (* auto now too slow without trace *)
]
qed.

lemma lbotr_ldrop_trans_le: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → ∀dd,ee. ⊒[dd, ee] L1 →
                            dd + ee ≤ d → ⊒[dd, ee] L2.
#L1 #L2 #d #e #HL12 #dd #ee #HL1 #Hddee
@lbotr_ldrop #I #K2 #V2 #i #Hddi #Hiddee #HLK2
lapply (lt_to_le_to_lt … Hiddee Hddee) -Hddee #Hid
elim (ldrop_trans_le … HL12 … HLK2 ?) -L2 /2 width=2/ #X #HLK1 #H
elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #K1 #V1 #HK12 #HV21 #H destruct
@(lbotr_inv_ldrop … HLK1 … HL1) -L1 -K1 -V1 //
qed.

lemma lbotr_ldrop_trans_be_up: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 →
                               ∀dd,ee. ⊒[dd, ee] L1 →
                               dd ≤ d + e → d + e ≤ dd + ee →
                               ⊒[d, dd + ee - d - e] L2.
#L1 #L2 #d #e #HL12 #dd #ee #HL1 #Hdde #Hddee
@lbotr_ldrop #I #K2 #V2 #i #Hdi #Hiddee #HLK2
lapply (transitive_le ? ? (i+e)… Hdde ?) -Hdde /2 width=1/ #Hddie
>commutative_plus in Hiddee; >minus_minus_comm <plus_minus_m_m /2 width=1/ -Hddee #Hiddee
lapply (ldrop_trans_ge … HL12 … HLK2 ?) -L2 // -Hdi  #HL1K2
@(lbotr_inv_ldrop … HL1K2 … HL1) -L1 >commutative_plus // -Hddie /2 width=1/
qed.

lemma lbotr_ldrop_trans_ge: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → ∀dd,ee. ⊒[dd, ee] L1 →
                            d + e ≤ dd → ⊒[dd - e, ee] L2.
#L1 #L2 #d #e #HL12 #dd #ee #HL1 #Hddee
@lbotr_ldrop #I #K2 #V2 #i #Hddi #Hiddee #HLK2
elim (le_inv_plus_l … Hddee) -Hddee #Hdde #Hedd
>plus_minus in Hiddee; // #Hiddee
lapply (transitive_le … Hdde Hddi) -Hdde #Hid
lapply (ldrop_trans_ge … HL12 … HLK2 ?) -L2 // -Hid #HL1K2
@(lbotr_inv_ldrop … HL1K2 … HL1) -L1 >commutative_plus /2 width=1/
qed.
