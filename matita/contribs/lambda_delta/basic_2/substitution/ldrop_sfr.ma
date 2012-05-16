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

include "basic_2/substitution/lsubs_sfr.ma".
include "basic_2/substitution/ldrop.ma".

(* DROPPING *****************************************************************)

(* Properties about local env. full refinement for substitution *************)

lemma sfr_ldrop: ∀L,d,e.
                 (∀I,K,V,i. d ≤ i → i < d + e → ⇩[0, i] L ≡ K. ⓑ{I}V → I = Abbr) →
                 ≼ [d, e] L.
#L elim L -L //
#L #I #V #IHL #d @(nat_ind_plus … d) -d
[ #e @(nat_ind_plus … e) -e //
  #e #_ #HH
  >(HH I L V 0 ? ? ?) // /5 width=6/
| /5 width=6/
]
qed.

(* Inversion lemmas about local env. full refinement for substitution *******)

lemma sfr_inv_ldrop: ∀I,L,K,V,i. ⇩[0, i] L ≡ K. ⓑ{I}V → ∀d,e. ≼ [d, e] L →
                     d ≤ i → i < d + e → I = Abbr.
#I #L elim L -L
[ #K #V #i #H
  lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L #J #W #IHL #K #V #i #H
  elim (ldrop_inv_O1 … H) -H *
  [ -IHL #H1 #H2 #d #e #HL #Hdi #Hide destruct
    lapply (le_n_O_to_eq … Hdi) -Hdi #H destruct
    lapply (HL … (L.ⓓW) ?) -HL /2 width=1/ #H
    elim (lsubs_inv_abbr1 … H ?) -H // -Hide #K #_ #H destruct //
  | #Hi #HLK #d @(nat_ind_plus … d) -d
    [ #e #H #_ #Hide
      elim (sfr_inv_bind … H ?) -H [2: /2 width=2/ ] #HL #H destruct
      @(IHL … HLK … HL) -IHL -HLK -HL // /2 width=1/
    | #d #_ #e #H #Hdi #Hide
      lapply (sfr_inv_skip … H ?) -H // #HL
      @(IHL … HLK … HL) -IHL -HLK -HL /2 width=1/
    ]
  ]
]
qed-.
