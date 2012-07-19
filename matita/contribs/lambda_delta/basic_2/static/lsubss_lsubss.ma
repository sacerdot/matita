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

include "basic_2/static/lsubss_ssta.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STATIC TYPE ASSIGNMENT ******************)

(* Main properties **********************************************************)

theorem lsubss_trans: ∀h,g,L1,L. h ⊢ L1 •⊑[g] L → ∀L2. h ⊢ L •⊑[g] L2 →
                      h ⊢ L1 •⊑[g] L2.
#h #g #L1 #L #H elim H -L1 -L
[ #X #H >(lsubss_inv_atom1 … H) -H //
| #I #L1 #L #W #HL1 #IHL1 #X #H
  elim (lsubss_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=1/
  | #V #l #H1WV #H2WV #HL2 #H1 #H2 destruct /3 width=3/
  ]
| #L1 #L #V1 #W1 #l #H1VW1 #H2VW1 #HL1 #IHL1 #X #H
  elim (lsubss_inv_pair1 … H) -H * #L2
  [ #HL2 #H destruct /3 width=5/
  | #V #l0 #_ #_ #_ #_ #H destruct
  ]
]
qed.
