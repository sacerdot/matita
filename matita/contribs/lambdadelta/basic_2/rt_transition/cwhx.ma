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

include "basic_2/notation/relations/predtywhead_5.ma".
include "static_2/syntax/item_sd.ma".
include "static_2/syntax/lenv.ma".
include "static_2/syntax/genv.ma".

(* WHD NORMAL TERMS FOR UNBOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ****)

inductive cwhx (h) (o:sd h) (G:genv): relation2 lenv term ≝
| cwhx_sort: ∀L,s. cwhx h o G L (⋆s)
| cwhx_abst: ∀p,L,W,T. cwhx h o G L (ⓛ{p}W.T)
| cwhx_neg : ∀L,V,T. cwhx h o G (L.ⓓV) T → cwhx h o G L (-ⓓV.T)
.

interpretation
   "whd normality for unbound context-sensitive parallel rt-transition (term)"
   'PRedTyWHead h o G L T = (cwhx h o G L T).

(* Basic inversion lemmas ***************************************************)

fact cwhx_inv_lref_aux (h) (o) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃X⦄ →
                       ∀i. X = #i → ⊥.
#h #o #G #Y #X * - X -Y
[ #L #s #i #H destruct
| #p #L #W #T #i #H destruct
| #L #V #T #_ #i #H destruct
]
qed-.

lemma cwhx_inv_lref (h) (o) (G):
                    ∀L,i. ⦃G,L⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃#i⦄ → ⊥.
/2 width=8 by cwhx_inv_lref_aux/ qed-.

fact cwhx_inv_gref_aux (h) (o) (G):
                       ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃X⦄ →
                       ∀l. X = §l → ⊥.
#h #o #G #Y #X * - X -Y
[ #L #s #l #H destruct
| #p #L #W #T #l #H destruct
| #L #V #T #_ #l #H destruct
]
qed-.

lemma cwhx_inv_gref (h) (o) (G):
                    ∀L,l. ⦃G,L⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃§l⦄ → ⊥.
/2 width=8 by cwhx_inv_gref_aux/ qed-.

fact cwhx_inv_pos_aux (h) (o) (G):
                      ∀Y,X. ⦃G,Y⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃X⦄ →
                      ∀W,U. X = +ⓓW.U → ⊥.
#h #o #G #Y #X * - X -Y
[ #L #s #X1 #X2 #H destruct
| #p #L #W #T #X1 #X2 #H destruct
| #L #V #T #_ #X1 #X2 #H destruct
]
qed-.

lemma cwhx_inv_pos (h) (o) (G):
                   ∀Y,V,T. ⦃G,Y⦄ ⊢ ⬈[h,o] 𝐖𝐇⦃+ⓓV.T⦄ → ⊥.
/2 width=9 by cwhx_inv_pos_aux/ qed-.
