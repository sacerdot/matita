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

include "basic_2A/substitution/drop_append.ma".
include "basic_2A/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties on append for local environments ******************************)

lemma frees_append: āL2,U,l,i. L2 ā¢ i Ļµ š*[l]ā¦Uā¦ ā i ā¤ |L2| ā
                    āL1. L1 ā L2 ā¢ i Ļµ š*[l]ā¦Uā¦.
#L2 #U #l #i #H elim H -L2 -U -l -i /3 width=2 by frees_eq/
#I #L2 #K2 #U #W #l #i #j #Hlj #Hji #HnU #HLK2 #_ #IHW #Hi #L1
lapply (drop_fwd_length_minus2 ā¦ HLK2) normalize #H0
lapply (drop_O1_append_sn_le ā¦ HLK2 ā¦ L1) -HLK2
[ -I -L1 -K2 -U -W -l /3 width=3 by lt_to_le, lt_to_le_to_lt/
| #HLK2 @(frees_be ā¦ HnU HLK2) // -HnU -HLK2 @IHW -IHW
  >(minus_plus_m_m (|K2|) 1) >H0 -H0 /2 width=1 by monotonic_le_minus_l2/
]
qed.

(* Inversion lemmas on append for local environments ************************)

fact frees_inv_append_aux: āL,U,l,i. L ā¢ i Ļµ š*[l]ā¦Uā¦ ā āL1,L2. L = L1 ā L2 ā
                           i ā¤ |L2| ā L2 ā¢ i Ļµ š*[l]ā¦Uā¦.
#L #U #l #i #H elim H -L -U -l -i /3 width=2 by frees_eq/
#Z #L #Y #U #X #l #i #j #Hlj #Hji #HnU #HLY #_ #IHW #L1 #L2 #H #Hi destruct
elim (drop_O1_lt (ā») L2 j) [2: -Z -Y -L1 -X -U -l /2 width=3 by lt_to_le_to_lt/ ]
#I #K2 #W #HLK2 lapply (drop_fwd_length_minus2 ā¦ HLK2) normalize #H0
lapply (drop_O1_inv_append1_le ā¦ HLY ā¦ HLK2) -HLY
[ -Z -I -Y -K2 -L1 -X -U -W -l /3 width=3 by lt_to_le, lt_to_le_to_lt/
| normalize #H destruct
  @(frees_be ā¦ HnU HLK2) -HnU -HLK2 // @IHW -IHW //
  >(minus_plus_m_m (|K2|) 1) >H0 -H0 /2 width=1 by monotonic_le_minus_l2/
]
qed-.

lemma frees_inv_append: āL1,L2,U,l,i. L1 ā L2 ā¢ i Ļµ š*[l]ā¦Uā¦ ā
                        i ā¤ |L2| ā L2 ā¢ i Ļµ š*[l]ā¦Uā¦.
/2 width=4 by frees_inv_append_aux/ qed-.
