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

include "basic_2/substitution/lsubs.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR SUBSTITUTION ****************************)

(* bottom element of the refinement *)
definition sfr: nat → nat → predicate lenv ≝
   λd,e. NF_sn … (lsubs d e) (lsubs d e …).

interpretation
   "local environment full refinement (substitution)"
   'SubEqBottom d e L = (sfr d e L).

(* Basic properties *********************************************************)

lemma sfr_atom: ∀d,e. ≽ [d, e] ⋆.
#d #e #L #H
elim (lsubs_inv_atom2 … H) -H
[ #H destruct //
| * #H1 #H2 destruct //
]
qed.

lemma sfr_OO: ∀L. ≽ [0, 0] L.
// qed.

lemma sfr_abbr: ∀L,V,e. ≽ [0, e] L → ≽ [0, e + 1] L.ⓓV.
#L #V #e #HL #K #H
elim (lsubs_inv_abbr2 … H ?) -H // <minus_plus_m_m #X #HLX #H destruct
lapply (HL … HLX) -HL -HLX /2 width=1/
qed.

lemma sfr_abbr_O: ∀L,V. ≽[0,1] L.ⓓV.
#L #V
@(sfr_abbr … 0) //
qed.

lemma sfr_skip: ∀I,L,V,d,e. ≽ [d, e] L → ≽ [d + 1, e] L.ⓑ{I}V.
#I #L #V #d #e #HL #K #H
elim (lsubs_inv_skip2 … H ?) -H // <minus_plus_m_m #J #X #W #HLX #H destruct
lapply (HL … HLX) -HL -HLX /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

lemma sfr_inv_bind: ∀I,L,V,e. ≽ [0, e] L.ⓑ{I}V → 0 < e →
                    ≽ [0, e - 1] L ∧ I = Abbr.
#I #L #V #e #HL #He
lapply (HL (L.ⓓV) ?) /2 width=1/ #H
elim (lsubs_inv_abbr2 … H ?) -H // #K #_ #H destruct
@conj // #L #HKL
lapply (HL (L.ⓓV) ?) -HL /2 width=1/ -HKL #H
elim (lsubs_inv_abbr2 … H ?) -H // -He #X #HLX #H destruct //
qed-.

lemma sfr_inv_skip: ∀I,L,V,d,e. ≽ [d, e] L.ⓑ{I}V → 0 < d → ≽ [d - 1, e] L.
#I #L #V #d #e #HL #Hd #K #HLK
lapply (HL (K.ⓑ{I}V) ?) -HL /2 width=1/ -HLK #H
elim (lsubs_inv_skip2 … H ?) -H // -Hd #J #X #W #HKX #H destruct //
qed-.