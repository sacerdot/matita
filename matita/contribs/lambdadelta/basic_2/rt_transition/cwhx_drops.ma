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

include "static_2/relocation/drops.ma".
include "basic_2/rt_transition/cwhx.ma".

(* WHD NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ****)

(* Properties with generic slicing ******************************************)

lemma cwhx_lifts (h) (G): d_liftable1 … (cwhx h G).
#h #G #K #T #H elim H -K -T
[ #K #s #b #f #L #HLK #X #H
  lapply (lifts_inv_sort1 … H) -H #H destruct //
| #p #K #V #T #b #f #L #HLK #X #H
  elim (lifts_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct //
| #K #V #T #_ #IH #b #f #L #HLK #X #H
  elim (lifts_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct
  /5 width=4 by cwhx_ldef, drops_skip, ext2_pair/
]
qed-.

(* Inversion lemmas with generic slicing ************************************)

lemma cwhx_inv_lifts (h) (G): d_deliftable1 … (cwhx h G).
#h #G #L #U #H elim H -L -U
[ #L #s #b #f #K #HLK #X #H
  lapply (lifts_inv_sort2 … H) -H #H destruct //
| #p #L #W #U #b #f #K #HLK #X #H
  elim (lifts_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct //
| #L #W #U #_ #IH #b #f #K #HLK #X #H
  elim (lifts_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct
  /5 width=4 by cwhx_ldef, drops_skip, ext2_pair/
]
qed-.
